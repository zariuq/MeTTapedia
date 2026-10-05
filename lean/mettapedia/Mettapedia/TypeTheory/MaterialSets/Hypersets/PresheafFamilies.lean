import Mettapedia.TypeTheory.MaterialSets.Hypersets.MembershipEvidence
import Mettapedia.TypeTheory.DisplayedPresheafSlice
import Mettapedia.TypeTheory.DisplayedPresheafSupport
import Mathlib.CategoryTheory.Category.Preorder

/-!
# Contextual families of material hypersets

A family assigns a material hyperset to each element of a presheaf context,
and supplies functorial maps of its actual members along contextual arrows.
It therefore determines an existing displayed presheaf family, its genuine
comprehension object in the slice, and the predicate that a material member
exists. The incidence presentation of comprehension retains both the context
value and the material member; observing support forgets the member.

Membership in `HSet` is propositional. This makes two proofs of membership
of the same member interchangeable; it does not make the member carrier or
the displayed family a proposition. No representation of an arbitrary
presheaf family by a small material hyperset is asserted. `HSet.{w}` and its
member carriers live in `Type (w + 1)`, which is also the ambient universe of
the presheaf context used here.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.PresheafFamilies

open CategoryTheory
open Mettapedia.Computability.ComputationalTrinity
open Mettapedia.TypeTheory.DisplayedPresheafTransport
open Mettapedia.TypeTheory.DisplayedPresheafComprehension
open Mettapedia.TypeTheory.DisplayedPresheafCwf
open Mettapedia.TypeTheory.DisplayedPresheafSlice
open Mettapedia.GSLT.Topos

universe u v w

variable {Context : Type u} [Category.{v} Context]

/-- Material members retain their hyperset value. Only the proof of its
membership is proof irrelevant. -/
abbrev MaterialMembers (X : HSet.{w}) := {x : HSet.{w} // x ∈ X}

/-- The subtype presentation has the same actual members and evidence as
the generic material-membership dependent sum. No representative graph or
choice of a member is involved. -/
def membersEquivEl (X : HSet.{w}) :
    MaterialMembers X ≃ El (fun x Y : HSet.{w} => x ∈ Y) X where
  toFun member := ⟨member.val, member.property⟩
  invFun member := ⟨member.1, member.2⟩
  left_inv member := by cases member; rfl
  right_inv member := by cases member; rfl

@[simp] theorem membersEquivEl_fst (X : HSet.{w}) (member : MaterialMembers X) :
    (membersEquivEl X member).1 = member.val := rfl

/-- A context-dependent family of material sets with coherent member maps.
These maps are data, not inferred from a bare implication of inhabitation. -/
structure MemberFamily (base : Face.{u, v, w + 1} Context) where
  sets : base.Elements → HSet.{w}
  restriction : ∀ {source target : base.Elements},
    (source ⟶ target) → MaterialMembers (sets source) → MaterialMembers (sets target)
  restriction_id : ∀ (point : base.Elements) (member : MaterialMembers (sets point)),
    restriction (𝟙 point) member = member
  restriction_comp : ∀ {first middle last : base.Elements}
    (earlier : first ⟶ middle) (later : middle ⟶ last)
    (member : MaterialMembers (sets first)),
    restriction (earlier ≫ later) member = restriction later (restriction earlier member)

namespace MemberFamily

variable {base : Face.{u, v, w + 1} Context} (family : MemberFamily base)

/-- The actual material-member carrier and action, as the displayed family
used by the presheaf CwF. -/
def displayed : DisplayedFamily.{u, v, w + 1, w + 1} base where
  obj point := MaterialMembers (family.sets point)
  map arrow := TypeCat.ofHom (family.restriction arrow)
  map_id point := by
    apply ConcreteCategory.hom_ext
    exact family.restriction_id point
  map_comp earlier later := by
    apply ConcreteCategory.hom_ext
    exact family.restriction_comp earlier later

/-- The members of nested sets form a contextual family by inclusion. Its
restriction preserves the actual member value. -/
def ofInclusions (sets : base.Elements → HSet.{w})
    (stable : ∀ {source target : base.Elements} (_arrow : source ⟶ target)
      {member : HSet.{w}}, member ∈ sets source → member ∈ sets target) :
    MemberFamily base where
  sets := sets
  restriction arrow member := ⟨member.val, stable arrow member.property⟩
  restriction_id _ _ := Subtype.ext rfl
  restriction_comp _ _ _ := Subtype.ext rfl

/-- Natural base substitution reindexes the assigned sets and their actual
member maps through the induced functor on categories of elements. -/
def reindex {replacement : Face.{u, v, w + 1} Context}
    (substitution : replacement ⟶ base) : MemberFamily replacement where
  sets point := family.sets (substitution.mapElements.obj point)
  restriction arrow := family.restriction (substitution.mapElements.map arrow)
  restriction_id point member := by
    rw [CategoryTheory.Functor.map_id]
    exact family.restriction_id _ member
  restriction_comp earlier later member := by
    rw [CategoryTheory.Functor.map_comp]
    exact family.restriction_comp _ _ member

/-- Reindexing the material family has the same objects and restriction
maps as actual CwF substitution of its displayed member family. -/
theorem displayed_reindex {replacement : Face.{u, v, w + 1} Context}
    (substitution : replacement ⟶ base) :
    (family.reindex substitution).displayed =
      reindexDisplayed substitution family.displayed := by
  rfl

/-- The incidence carrier of a context value and a material member. -/
abbrev IncidenceAt (context : Contextᵒᵖ) :=
  { pair : base.obj context × HSet.{w} //
    pair.2 ∈ family.sets ⟨context, pair.1⟩ }

/-- Comprehension's dependent pair and material incidence encode the same
context value and member, with explicit inverse maps. -/
def incidenceEquiv (context : Contextᵒᵖ) :
    TotalAt family.displayed context ≃ family.IncidenceAt context where
  toFun value := ⟨(value.1, value.2.val), value.2.property⟩
  invFun value := ⟨value.1.1, ⟨value.1.2, value.2⟩⟩
  left_inv value := by cases value; rfl
  right_inv value := by cases value; rfl

/-- Incidence restriction transports the member using the supplied family
map, as well as transporting its context value. -/
def incidenceMap {source target : Contextᵒᵖ}
    (arrow : source ⟶ target) (value : family.IncidenceAt source) :
    family.IncidenceAt target :=
  family.incidenceEquiv target
    (totalMap family.displayed arrow ((family.incidenceEquiv source).symm value))

/-- Incidence is a genuine presheaf, including nonconstant member fibres. -/
def incidence : Face.{u, v, w + 1} Context where
  obj := family.IncidenceAt
  map arrow := TypeCat.ofHom (family.incidenceMap arrow)
  map_id context := by
    apply ConcreteCategory.hom_ext
    intro value
    apply (family.incidenceEquiv context).symm.injective
    exact totalMap_id family.displayed context _
  map_comp earlier later := by
    apply ConcreteCategory.hom_ext
    intro value
    apply (family.incidenceEquiv _).symm.injective
    exact totalMap_comp family.displayed earlier later _

/-- The comparison is natural on contextual restrictions; it preserves the
actual member rather than replacing it by an existence proof. -/
def incidenceIso : totalSpace family.displayed ≅ family.incidence where
  hom := {
    app context := TypeCat.ofHom (family.incidenceEquiv context)
    naturality := by
      intro source target arrow
      apply ConcreteCategory.hom_ext
      intro value
      rfl }
  inv := {
    app context := TypeCat.ofHom (family.incidenceEquiv context).symm
    naturality := by
      intro source target arrow
      apply ConcreteCategory.hom_ext
      intro value
      rfl }
  hom_inv_id := by
    ext context value
    rfl
  inv_hom_id := by
    ext context value
    rfl

/-- Forget the material member while retaining the context value. -/
def incidenceProjection : family.incidence ⟶ base where
  app _ := TypeCat.ofHom (fun value => value.val.1)
  naturality := by
    intro source target arrow
    apply ConcreteCategory.hom_ext
    intro value
    rfl

/-- Incidence and CwF comprehension have the same projection. -/
theorem incidenceIso_projection :
    family.incidenceIso.hom ≫ family.incidenceProjection =
      totalProjection family.displayed := by
  ext context value
  rfl

/-- Material incidence is the displayed family--slice comparison over the
same base, not merely an equivalence of unindexed carriers. -/
def incidenceSliceIso :
    (totalFunctor base).obj family.displayed ≅ Over.mk family.incidenceProjection :=
  Over.isoMk family.incidenceIso family.incidenceIso_projection

/-- A natural member section is precisely a slice map into material
incidence, retaining the selected member at every contextual point. -/
def memberTermEquiv :
    family.displayed.sections ≃
      (Over.mk (𝟙 base) ⟶ Over.mk family.incidenceProjection) where
  toFun term := (termEquiv family.displayed term) ≫ family.incidenceSliceIso.hom
  invFun arrow := (termEquiv family.displayed).symm
    (arrow ≫ family.incidenceSliceIso.inv)
  left_inv term := by simp
  right_inv arrow := by simp

/-- The comparison's term map contains the original chosen material member. -/
theorem memberTermEquiv_value (term : family.displayed.sections)
    (context : Contextᵒᵖ) (value : base.obj context) :
    ((family.memberTermEquiv term).left.app context value).val.2 =
      (term.val ⟨context, value⟩).val := by
  rfl

/-- This predicate states existence of a material member. It does not
supply a natural member section or select one member from each fibre. -/
def inhabitedPredicate : Subfunctor base where
  obj context := { value | ∃ member, member ∈ family.sets ⟨context, value⟩ }
  map {source target} arrow := by
    rintro value ⟨member, belongs⟩
    let transported := family.restriction
      (CategoryOfElements.homMk
        (⟨source, value⟩ : base.Elements)
        (⟨target, base.map arrow value⟩ : base.Elements) arrow rfl) ⟨member, belongs⟩
    exact ⟨transported.val, transported.property⟩

/-- Support of the existing displayed family is exactly inhabited material
membership, including its natural restriction action. -/
theorem support_eq_inhabitedPredicate :
    support family.displayed = family.inhabitedPredicate := by
  ext context value
  constructor
  · rintro ⟨member⟩
    exact ⟨member.val, member.property⟩
  · rintro ⟨member, belongs⟩
    exact ⟨⟨member, belongs⟩⟩

/-- The range of material incidence is the same support predicate. -/
theorem incidence_range_eq_inhabitedPredicate :
    Subfunctor.range family.incidenceProjection = family.inhabitedPredicate := by
  ext context value
  constructor
  · rintro ⟨member, same⟩
    change member.val.1 = value at same
    exact ⟨member.val.2, same ▸ member.property⟩
  · rintro ⟨member, belongs⟩
    exact ⟨⟨(value, member), belongs⟩, rfl⟩

/-- Existence observation commutes with actual context substitution. -/
theorem inhabitedPredicate_reindex {replacement : Face.{u, v, w + 1} Context}
    (substitution : replacement ⟶ base) :
    (family.reindex substitution).inhabitedPredicate =
      family.inhabitedPredicate.preimage substitution := by
  rw [← support_eq_inhabitedPredicate, displayed_reindex]
  change support (substitution.mapElements ⋙ family.displayed) = _
  rw [support_reindex, support_eq_inhabitedPredicate]

/-- The member carrier is a subtype of material sets: equality of two
membership proofs alone is irrelevant, but equality of members is required. -/
theorem member_eq_iff (point : base.Elements)
    (first second : family.displayed.obj point) :
    first = second ↔ first.val = second.val :=
  ⟨congrArg Subtype.val, Subtype.ext⟩

end MemberFamily

/-! ## Nonconstant material families with actual restriction arrows -/

namespace Controls

/-- The context category is the reverse two-stage order. Its presheaves
have a restriction from stage zero to stage one. -/
abbrev StageContext := OrderDual (Fin 2)

def base : Face.{0, 0, 1} StageContext where
  obj _ := PUnit.{2}
  map _ := TypeCat.ofHom id
  map_id _ := rfl
  map_comp _ _ := rfl

def zeroPoint : base.Elements := ⟨Opposite.op (0 : StageContext), PUnit.unit⟩
def onePoint : base.Elements := ⟨Opposite.op (1 : StageContext), PUnit.unit⟩

def step : zeroPoint ⟶ onePoint :=
  CategoryOfElements.homMk _ _
    (homOfLE (show (1 : StageContext) ≤ 0 from by decide)).op rfl

/-- An inclusion of material sets gives a nonconstant two-stage family.
The only nonidentity restriction acts by this supplied inclusion. -/
def twoStage (first second : HSet.{0})
    (included : ∀ {member : HSet.{0}}, member ∈ first → member ∈ second) :
    MemberFamily base :=
  MemberFamily.ofInclusions
    (fun point => if point.1.unop = 0 then first else second)
    (by
      intro source target arrow member belongs
      have stages := leOfHom arrow.val.unop
      change source.1.unop.val ≤ target.1.unop.val at stages
      by_cases sourceZero : source.1.unop = 0
      · by_cases targetZero : target.1.unop = 0
        · simpa only [sourceZero, targetZero, if_pos] using belongs
        · simpa [targetZero] using
            (included (by simpa [sourceZero] using belongs))
      · have targetNonzero : target.1.unop ≠ 0 := by
          intro targetZero
          apply sourceZero
          apply Fin.ext
          rw [targetZero] at stages
          change source.1.unop.val ≤ 0 at stages
          exact Nat.eq_zero_of_le_zero stages
        simpa only [sourceZero, targetNonzero, if_neg] using belongs)

/-- Empty and singleton material fibres form a valid contextual family. -/
def emptyToSingleton : MemberFamily base :=
  twoStage ∅ {∅} (fun {member} belongs => (HSet.notMem_empty member belongs).elim)

theorem zero_fibre_empty : ¬ Nonempty (emptyToSingleton.displayed.obj zeroPoint) := by
  rintro ⟨member⟩
  exact HSet.notMem_empty member.val member.property

def oneMember : emptyToSingleton.displayed.obj onePoint :=
  ⟨∅, HSet.mem_singleton_self ∅⟩

theorem one_fibre_inhabited : Nonempty (emptyToSingleton.displayed.obj onePoint) :=
  ⟨oneMember⟩

theorem no_global_member_section : ¬ Nonempty emptyToSingleton.displayed.sections := by
  rintro ⟨sectionValue⟩
  exact zero_fibre_empty ⟨sectionValue.val zeroPoint⟩

theorem no_reverse_member_map :
    ¬ Nonempty (emptyToSingleton.displayed.obj onePoint →
      emptyToSingleton.displayed.obj zeroPoint) := by
  rintro ⟨reverse⟩
  exact zero_fibre_empty ⟨reverse oneMember⟩

theorem zero_not_supported :
    zeroPoint.2 ∉ (support emptyToSingleton.displayed).obj zeroPoint.1 :=
  zero_fibre_empty

theorem one_supported :
    onePoint.2 ∈ (support emptyToSingleton.displayed).obj onePoint.1 :=
  one_fibre_inhabited

/-- At both stages there are actual members, and the restriction carries
the empty hyperset into a strictly larger member carrier. -/
def singletonToPair : MemberFamily base :=
  twoStage {∅} {∅, {∅}}
    (fun belongs => HSet.mem_insert_iff.mpr (Or.inl (HSet.mem_singleton.mp belongs)))

def firstMember : singletonToPair.displayed.obj zeroPoint :=
  ⟨∅, HSet.mem_singleton_self ∅⟩

def retainedMember : singletonToPair.displayed.obj onePoint :=
  ⟨∅, HSet.mem_insert_iff.mpr (Or.inl rfl)⟩

def newMember : singletonToPair.displayed.obj onePoint :=
  ⟨{∅}, HSet.mem_insert_iff.mpr (Or.inr (HSet.mem_singleton_self {∅}))⟩

theorem step_retains_material_member :
    singletonToPair.displayed.map step firstMember = retainedMember :=
  Subtype.ext rfl

theorem later_members_distinct : retainedMember ≠ newMember := by
  intro same
  exact HSet.empty_ne_singleton_empty (congrArg Subtype.val same)

theorem later_fibre_not_subsingleton :
    ¬ Subsingleton (singletonToPair.displayed.obj onePoint) :=
  fun all => later_members_distinct (all.elim _ _)

/-- A bare inhabitance proof cannot recover every original material
member. This failure concerns distinct members, not distinct proofs of
one membership proposition. -/
theorem no_member_recovery_from_inhabitation :
    ¬ ∃ recover : Nonempty (singletonToPair.displayed.obj onePoint) →
        singletonToPair.displayed.obj onePoint,
      ∀ member, recover ⟨member⟩ = member := by
  rintro ⟨recover, recovers⟩
  apply later_members_distinct
  calc
    retainedMember = recover ⟨retainedMember⟩ := (recovers retainedMember).symm
    _ = recover ⟨newMember⟩ := rfl
    _ = newMember := recovers newMember

/-- The support observation identifies two different material members.
Membership proof irrelevance does not justify this loss for a member-valued
dependent consumer. -/
theorem incidence_projection_forgets_members :
    (singletonToPair.incidenceEquiv onePoint.1 ⟨onePoint.2, retainedMember⟩) ≠
      (singletonToPair.incidenceEquiv onePoint.1 ⟨onePoint.2, newMember⟩) ∧
    singletonToPair.incidenceProjection.app onePoint.1
        (singletonToPair.incidenceEquiv onePoint.1 ⟨onePoint.2, retainedMember⟩) =
      singletonToPair.incidenceProjection.app onePoint.1
        (singletonToPair.incidenceEquiv onePoint.1 ⟨onePoint.2, newMember⟩) := by
  constructor
  · intro same
    exact HSet.empty_ne_singleton_empty
      (congrArg (fun value : singletonToPair.IncidenceAt onePoint.1 => value.val.2) same)
  · rfl

end Controls

#print axioms MemberFamily.incidenceSliceIso
#print axioms MemberFamily.incidenceIso
#print axioms membersEquivEl
#print axioms MemberFamily.memberTermEquiv
#print axioms MemberFamily.support_eq_inhabitedPredicate
#print axioms MemberFamily.inhabitedPredicate_reindex
#print axioms Controls.no_reverse_member_map
#print axioms Controls.base
#print axioms Controls.no_global_member_section
#print axioms Controls.step_retains_material_member
#print axioms Controls.incidence_projection_forgets_members
#print axioms Controls.no_member_recovery_from_inhabitation

end Mettapedia.TypeTheory.MaterialSets.Hypersets.PresheafFamilies
