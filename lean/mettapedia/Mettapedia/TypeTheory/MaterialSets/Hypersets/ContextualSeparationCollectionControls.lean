import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualSeparationCollection
import Mettapedia.TypeTheory.MaterialSets.Hypersets.NaturalOrdinalModel
import Mettapedia.GSLT.Logic.ObservedGeneratedModelControls

/-!
# Nonconstant separation and collection controls

Singleton separation follows an actual varying section on the infinite
labelled-path model, retaining its empty and cyclic readings. A separate
infinite-action control has one world with natural-number loop arrows and
the entire constructed material natural carrier. Each loop advances its
members. Every fibre is inhabited, but there is no natural section.

The all-witness typed collection projection in this model is surjective
at every point while its row family has no natural section. Coverage does
not manufacture coherent dependent choice. No inverse decoder from material
natural members to host natural numbers is chosen or assumed.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualSeparationCollectionControls

open _root_.CategoryTheory ContextualGeneratedUniverse ContextualSeparationCollection AccessiblePointedGraph
open Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent

universe u

namespace Varying

open Mettapedia.GSLT.ObservedGeneratedModelControls.Paths
open Mettapedia.GSLT.ObservedGeneratedModel

def separated := separate observedInput (StablePredicate.equalTo observedInput positiveSection)

theorem old_carrier : (separated.model (observedPoint model worldCoding oldRaw)).carrier = {∅} :=
  (Controls.equalTo_carrier observedInput positiveSection _).trans
    (congrArg (fun value : HSet => ({value} : HSet)) old_section_value)

theorem later_carrier : (separated.model (observedPoint model worldCoding newRaw)).carrier = {HSet.quineAtom} :=
  (Controls.equalTo_carrier observedInput positiveSection _).trans
    (congrArg (fun value : HSet => ({value} : HSet)) new_section_value)

theorem genuinely_varying :
    (separated.model (observedPoint model worldCoding oldRaw)).carrier ≠
      (separated.model (observedPoint model worldCoding newRaw)).carrier := by
  rw [old_carrier, later_carrier]
  exact fun same => HSet.empty_ne_quineAtom (HSet.singleton_inj.mp same)

theorem section_exists : Nonempty separated.family.sections :=
  Controls.equalTo_section observedInput positiveSection

end Varying

namespace Advancing

abbrev Site : Type u := ULift.{u, 0} PUnit

/-- The control has infinitely many distinct loop arrows, with addition as
their actual composition. The single object is not a collapsed arrow model. -/
instance siteCategory : Category.{u} Site where
  Hom _ _ := ULift.{u, 0} Nat
  id _ := ⟨0⟩
  comp first second := ⟨first.down + second.down⟩
  id_comp arrow := ULift.ext _ _ (Nat.zero_add arrow.down)
  comp_id arrow := ULift.ext _ _ (Nat.add_zero arrow.down)
  assoc first second third := ULift.ext _ _ (Nat.add_assoc first.down second.down third.down)

def base : Siteᵒᵖ ⥤ Type u where
  obj _ := ULift.{u, 0} PUnit
  map _ := TypeCat.ofHom id
  map_id _ := rfl
  map_comp _ _ := rfl

def context : LabelledContext Site where
  base := base
  labels := {
    graph _ := AccessiblePointedGraph.empty
    injective := by
      rintro ⟨X, first⟩ ⟨Y, second⟩ _
      have worlds : X = Y := Subsingleton.elim _ _
      cases worlds
      have terms : first = second := by
        exact @Subsingleton.elim (ULift.{u, 0} PUnit) inferInstance first second
      cases terms
      rfl }

def point : context.base.Elements := ⟨Opposite.op ⟨PUnit.unit⟩, ⟨PUnit.unit⟩⟩

def loop (atPoint : context.base.Elements) (number : Nat) : atPoint ⟶ atPoint :=
  ⟨(show atPoint.1.unop ⟶ atPoint.1.unop from ULift.up number).op, rfl⟩

theorem distinct_loops : loop point 0 ≠ loop point 1 := by
  intro same
  have numbers := congrArg (fun arrow : point ⟶ point => arrow.val.unop.down) same
  exact Nat.zero_ne_one numbers

def naturalGraph : AccessiblePointedGraph.{u} :=
  AccessiblePointedGraph.sup (fun number : ULift.{u, 0} Nat => NaturalOrdinalModel.graph number.down)

theorem naturalGraph_value : HSet.mk naturalGraph.{u} = NaturalOrdinalModel.naturals := rfl

abbrev NaturalMember := {value : HSet.{u} // value ∈ NaturalOrdinalModel.naturals}

def memberEquiv : PowerMemberClass naturalGraph.{u} ≃ NaturalMember where
  toFun code := ⟨(classMember naturalGraph code).val, by
    simpa only [AccessiblePointedGraph.picture_eq_mk, naturalGraph_value] using
      (classMember naturalGraph code).property⟩
  invFun member := classOfMember naturalGraph ⟨member.val, by
    simpa only [AccessiblePointedGraph.picture_eq_mk, naturalGraph_value] using member.property⟩
  left_inv code := classOfMember_classMember naturalGraph code
  right_inv member := by
    apply Subtype.ext
    exact congrArg (fun member : PicturedMembers naturalGraph => member.val)
      (classMember_classOfMember naturalGraph _)

def successorMember (member : NaturalMember.{u}) : NaturalMember :=
  ⟨NaturalOrdinalModel.successor member.val,
    NaturalOrdinalModel.successor_member_naturals member.property⟩

def advance : Nat → NaturalMember.{u} → NaturalMember
  | 0, member => member
  | number + 1, member => successorMember (advance number member)

theorem advance_add (first second : Nat) (member : NaturalMember.{u}) :
    advance (first + second) member = advance second (advance first member) := by
  induction second with
  | zero => rfl
  | succ second previous => exact congrArg successorMember previous

def advanceClass (number : Nat) (code : PowerMemberClass naturalGraph.{u}) : PowerMemberClass naturalGraph :=
  memberEquiv.symm (advance number (memberEquiv code))

@[simp] theorem advanceClass_zero (code : PowerMemberClass naturalGraph.{u}) : advanceClass 0 code = code :=
  memberEquiv.symm_apply_apply code

theorem advanceClass_add (first second : Nat) (code : PowerMemberClass naturalGraph.{u}) :
    advanceClass (first + second) code = advanceClass second (advanceClass first code) := by
  unfold advanceClass
  rw [Equiv.apply_symm_apply, advance_add]

def family : MaterialFamily context.{u} where
  family := {
    obj _ := PowerMemberClass naturalGraph
    map arrow := TypeCat.ofHom (advanceClass arrow.val.unop.down)
    map_id _ := by
      apply ConcreteCategory.hom_ext
      exact advanceClass_zero
    map_comp first second := by
      apply ConcreteCategory.hom_ext
      intro code
      change advanceClass (second.val.unop.down + first.val.unop.down) code =
        advanceClass second.val.unop.down (advanceClass first.val.unop.down code)
      rw [Nat.add_comm, advanceClass_add] }
  model _ := PowerClassContextualMaterialization.powerClassModel naturalGraph

def zeroClass : PowerMemberClass naturalGraph.{u} :=
  memberEquiv.symm ⟨∅, NaturalOrdinalModel.zero_member_naturals⟩

theorem all_fibres_inhabited (atPoint : context.{u}.base.Elements) :
    Nonempty (family.family.obj atPoint) := ⟨zeroClass⟩

theorem original_bound_carrier (atPoint : context.{u}.base.Elements) :
    (family.model atPoint).carrier = NaturalOrdinalModel.naturals := rfl

theorem advance_no_fixed_point (member : NaturalMember.{u}) : advance 1 member ≠ member := by
  intro same
  have sameValue : NaturalOrdinalModel.successor member.val = member.val :=
    congrArg Subtype.val same
  have selfMember : member.val ∈ NaturalOrdinalModel.successor member.val :=
    HSet.mem_insert_iff.mpr (Or.inl rfl)
  exact (NaturalOrdinalModel.naturals_wellFounded.mem member.property).notMem_self
    ((congrArg (fun carrier => member.val ∈ carrier) sameValue).mp selfMember)

theorem no_natural_section : ¬ Nonempty family.{u}.family.sections := by
  rintro ⟨term⟩
  have fixed := term.property (loop point 1)
  change advanceClass 1 (term.val point) = term.val point at fixed
  apply advance_no_fixed_point (memberEquiv (term.val point))
  exact (memberEquiv.apply_symm_apply _).symm.trans (congrArg memberEquiv fixed)

def domain : MaterialFamily context.{u} := MaterialFamily.unit context

def body : MaterialFamily domain.{u}.extension :=
  family.reindex (PowerClassPresheafProducts.projection domain.family)

def collected : MaterialFamily context.{u} :=
  rows domain body (StablePredicate.full body)

theorem collection_projection_covers (atPoint : context.{u}.base.Elements) :
    Function.Surjective ((projection domain body (StablePredicate.full body)).app atPoint) :=
  projection_surjective domain body (StablePredicate.full body) atPoint
    (fun _ => ⟨zeroClass, True.intro⟩)

/-- The row projection covers all arguments; its witnesses cannot be chosen
as one natural dependent section. This obstruction concerns coherence, not
existence of the all-witness material carrier. -/
theorem collected_no_natural_section : ¬ Nonempty collected.{u}.family.sections := by
  rintro ⟨term⟩
  have fixed := term.property (loop point 1)
  have fixedResult := congrArg (fun row : collected.family.obj point => row.2.val) fixed
  change advanceClass 1 ((term.val point).2.val) = (term.val point).2.val at fixedResult
  apply advance_no_fixed_point (memberEquiv ((term.val point).2.val))
  exact (memberEquiv.apply_symm_apply _).symm.trans (congrArg memberEquiv fixedResult)

end Advancing

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualSeparationCollectionControls
