import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGeneratedUniverse
import Mettapedia.TypeTheory.MaterialSets.Hypersets.PresentedSubtypes
import Mettapedia.TypeTheory.MaterialSets.Hypersets.PresentedCollection

/-!
# Constructed contextual separation and typed collection

A restriction-stable predicate on an actual material family constructs a
displayed subtype and its complete material member decoder at the original
graph bound. Its sections are exactly the original natural sections with
the predicate's evidence. Separation commutes with context substitution.

Dependent sums of these subtypes construct all relation witnesses. The
projection covers every argument when the relation is pointwise total;
this does not select a natural witness. For a stable functional relation,
the existing bounded separation-and-union computation constructs the unique
witness and proves its naturality. No section carrier or choice operation
is supplied. These are capabilities of the interpreted typed model, not
unrestricted fixed-level collection over the whole bare hyperset carrier.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualSeparationCollection

open CategoryTheory ContextualGeneratedUniverse
open Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent

universe u
variable {C : Type u} [Category.{u} C]
variable {context : LabelledContext C}

/-- Stability records the actual action of every context restriction. -/
structure StablePredicate (domain : MaterialFamily context) where
  holds : (point : context.base.Elements) → domain.family.obj point → Prop
  map : ∀ {first second : context.base.Elements} (arrow : first ⟶ second)
    (term : domain.family.obj first), holds first term →
      holds second (domain.family.map arrow term)

variable (domain : MaterialFamily context) (predicate : StablePredicate domain)

/-- Separation constructs both the displayed family and each material
decoder; predicate proofs remain in the decoded term. -/
def separate : MaterialFamily context where
  family := {
    obj point := {term : domain.family.obj point // predicate.holds point term}
    map arrow := TypeCat.ofHom (fun term =>
      ⟨domain.family.map arrow term.val, predicate.map arrow term.val term.property⟩)
    map_id point := by
      apply ConcreteCategory.hom_ext
      intro term
      apply Subtype.ext
      exact domain.family.map_id_apply point term.val
    map_comp first second := by
      apply ConcreteCategory.hom_ext
      intro term
      apply Subtype.ext
      exact domain.family.map_comp_apply first second term.val }
  model point := PresentedType.restrict (domain.model point) (predicate.holds point)

def inclusion : NatTrans (separate domain predicate).family domain.family where
  app _ := TypeCat.ofHom Subtype.val
  naturality _ _ _ := by
    apply ConcreteCategory.hom_ext
    intro _
    rfl

theorem inclusion_injective (point : context.base.Elements) :
    Function.Injective ((inclusion domain predicate).app point) :=
  Subtype.val_injective

theorem separated_value (point : context.base.Elements)
    (term : (separate domain predicate).family.obj point) :
    ((separate domain predicate).model point).value term =
      (domain.model point).value term.val := rfl

theorem separated_carrier (point : context.base.Elements) :
    ((separate domain predicate).model point).carrier =
      HSet.sep (PresentedType.encodedPredicate (domain.model point) (predicate.holds point))
        (domain.model point).carrier :=
  PresentedType.mk_restrictGraph (domain.model point) (predicate.holds point)

theorem mem_separated_carrier (point : context.base.Elements) (value : HSet.{u}) :
    value ∈ ((separate domain predicate).model point).carrier ↔
      ∃ term, predicate.holds point term ∧ (domain.model point).value term = value :=
  PresentedType.mem_restrict_carrier (domain.model point) (predicate.holds point) value

/-- Actual natural sections, rather than just positive support predicates. -/
def sectionEquiv : (separate domain predicate).family.sections ≃
    {term : domain.family.sections // ∀ point, predicate.holds point (term.val point)} where
  toFun term := ⟨⟨fun point => (term.val point).val, by
    intro first second arrow
    exact congrArg Subtype.val (term.property arrow)⟩,
    fun point => (term.val point).property⟩
  invFun term := ⟨fun point => ⟨term.val.val point, term.property point⟩, by
    intro first second arrow
    exact Subtype.ext (term.val.property arrow)⟩
  left_inv term := by
    apply Subtype.ext
    funext point
    apply Subtype.ext
    rfl
  right_inv term := by
    apply Subtype.ext
    apply Subtype.ext
    rfl

theorem sectionEquiv_value (term : (separate domain predicate).family.sections)
    (point : context.base.Elements) :
    ((sectionEquiv domain predicate term).val.val point) = (term.val point).val := rfl

namespace StablePredicate

def reindex {other : LabelledContext C} (change : NatTrans other.base context.base) :
    StablePredicate (domain.reindex change) where
  holds point := predicate.holds ((PowerClassPresheafProducts.elementMap change).obj point)
  map arrow term proof := predicate.map ((PowerClassPresheafProducts.elementMap change).map arrow)
    term proof

def full : StablePredicate domain where
  holds _ _ := True
  map _ _ _ := True.intro

def absent : StablePredicate domain where
  holds _ _ := False
  map _ _ proof := proof

/-- A section's singleton predicate respects every actual restriction. -/
def equalTo (term : domain.family.sections) : StablePredicate domain where
  holds point member := member = term.val point
  map arrow member same := by
    rw [same]
    exact term.property arrow

end StablePredicate

/-- The constructed subtype models use the transported original dictionaries,
so this comparison is equality of actual families, not just carrier equality. -/
theorem reindex_separate {other : LabelledContext C}
    (change : NatTrans other.base context.base) :
    (separate domain predicate).reindex change =
      separate (domain.reindex change) (predicate.reindex domain change) := rfl

/-! ## Functional stable relations construct actual natural sections -/

variable (total : ∀ point, ∃ term, predicate.holds point term)
variable (functional : ∀ point first second,
  predicate.holds point first → predicate.holds point second → first = second)

/-- This term is obtained by bounded material computation and the existing
member decoder, rather than extracting a witness from an existential proof. -/
def uniqueTerm (point : context.base.Elements) : domain.family.obj point :=
  PresentedCollection.uniqueSection PresentedType.unit
    (fun _ : ULift.{u, 0} PUnit => domain.model point)
    (fun _ => predicate.holds point) (fun _ => total point)
    (fun _ => functional point) ⟨PUnit.unit⟩

theorem uniqueTerm_spec (point : context.base.Elements) :
    predicate.holds point (uniqueTerm domain predicate total functional point) :=
  PresentedCollection.uniqueSection_spec PresentedType.unit
    (fun _ : ULift.{u, 0} PUnit => domain.model point)
    (fun _ => predicate.holds point) (fun _ => total point)
    (fun _ => functional point) ⟨PUnit.unit⟩

def uniqueSection : domain.family.sections :=
  ⟨uniqueTerm domain predicate total functional, by
    intro first second arrow
    exact functional second _ _
      (predicate.map arrow _ (uniqueTerm_spec domain predicate total functional first))
      (uniqueTerm_spec domain predicate total functional second)⟩

theorem uniqueSection_spec (point : context.base.Elements) :
    predicate.holds point ((uniqueSection domain predicate total functional).val point) :=
  uniqueTerm_spec domain predicate total functional point

theorem uniqueSection_unique (term : domain.family.sections)
    (satisfies : ∀ point, predicate.holds point (term.val point)) :
    term = uniqueSection domain predicate total functional := by
  apply Subtype.ext
  funext point
  exact functional point _ _ (satisfies point)
    (uniqueSection_spec domain predicate total functional point)

/-- Bounded unique decoding also commutes with substitution. Uniqueness is
used to compare the two constructed sections; no new witness is selected. -/
theorem uniqueTerm_reindex {other : LabelledContext C}
    (change : NatTrans other.base context.base) (point : other.base.Elements) :
    uniqueTerm (domain.reindex change) (predicate.reindex domain change)
        (fun point => total ((PowerClassPresheafProducts.elementMap change).obj point))
        (fun point => functional ((PowerClassPresheafProducts.elementMap change).obj point)) point =
      uniqueTerm domain predicate total functional
        ((PowerClassPresheafProducts.elementMap change).obj point) := by
  apply functional ((PowerClassPresheafProducts.elementMap change).obj point)
  · exact uniqueTerm_spec (domain.reindex change) (predicate.reindex domain change) _ _ point
  · exact uniqueTerm_spec domain predicate total functional _

/-! ## All-witness dependent collection -/

variable (body : MaterialFamily domain.extension) (relation : StablePredicate body)

def rows : MaterialFamily context := domain.sigma (separate body relation)

def projection : NatTrans (rows domain body relation).family domain.family where
  app _ := TypeCat.ofHom Sigma.fst
  naturality _ _ _ := by
    apply ConcreteCategory.hom_ext
    intro _
    rfl

theorem row_value (point : context.base.Elements) (argument : domain.family.obj point)
    (result : body.family.obj ⟨point.1, ⟨point.2, argument⟩⟩)
    (related : relation.holds ⟨point.1, ⟨point.2, argument⟩⟩ result) :
    ((rows domain body relation).model point).value ⟨argument, ⟨result, related⟩⟩ =
      HSet.kpair ((domain.model point).value argument)
        ((body.model ⟨point.1, ⟨point.2, argument⟩⟩).value result) :=
  PowerClassContextualMaterialization.sigmaModel_value _ _ _ _ _ _

theorem mem_rows (point : context.base.Elements) (value : HSet.{u}) :
    value ∈ ((rows domain body relation).model point).carrier ↔
      ∃ argument result, relation.holds ⟨point.1, ⟨point.2, argument⟩⟩ result ∧
        HSet.kpair ((domain.model point).value argument)
          ((body.model ⟨point.1, ⟨point.2, argument⟩⟩).value result) = value := by
  constructor
  · intro member
    let witness := ((rows domain body relation).model point).decode ⟨value, member⟩
    exact ⟨witness.1, witness.2.val, witness.2.property,
      (row_value domain body relation point witness.1 witness.2.val witness.2.property).symm.trans
        (((rows domain body relation).model point).value_decode _)⟩
  · rintro ⟨argument, result, related, same⟩
    exact ((row_value domain body relation point argument result related).trans same) ▸
      ((rows domain body relation).model point).value_mem ⟨argument, ⟨result, related⟩⟩

/-- Logical totality proves coverage of the actual row projection. It does
not choose a right inverse or a coherent natural section. -/
theorem projection_surjective (point : context.base.Elements)
    (covers : ∀ argument, ∃ result, relation.holds ⟨point.1, ⟨point.2, argument⟩⟩ result) :
    Function.Surjective ((projection domain body relation).app point) := by
  intro argument
  obtain ⟨result, related⟩ := covers argument
  exact ⟨⟨argument, ⟨result, related⟩⟩, rfl⟩

theorem projection_total_iff (point : context.base.Elements) :
    Function.Surjective ((projection domain body relation).app point) ↔
      ∀ argument, ∃ result, relation.holds ⟨point.1, ⟨point.2, argument⟩⟩ result := by
  constructor
  · intro covers argument
    obtain ⟨witness, same⟩ := covers argument
    change witness.1 = argument at same
    cases same
    exact ⟨witness.2.val, witness.2.property⟩
  · exact projection_surjective domain body relation point

namespace Controls

theorem equalTo_carrier (term : domain.family.sections) (point : context.base.Elements) :
    ((separate domain (StablePredicate.equalTo domain term)).model point).carrier =
      {(domain.model point).value (term.val point)} := by
  apply HSet.ext
  intro value
  rw [mem_separated_carrier, HSet.mem_singleton]
  constructor
  · rintro ⟨member, same, encoded⟩
    exact encoded.symm.trans (congrArg (domain.model point).value same)
  · intro same
    exact ⟨term.val point, rfl, same.symm⟩

theorem equalTo_section (term : domain.family.sections) :
    Nonempty (separate domain (StablePredicate.equalTo domain term)).family.sections :=
  ⟨(sectionEquiv domain (StablePredicate.equalTo domain term)).symm ⟨term, fun _ => rfl⟩⟩

theorem full_separation (point : context.base.Elements) :
    ((separate domain (StablePredicate.full domain)).model point).carrier =
      (domain.model point).carrier := PresentedType.restrict_true (domain.model point)

theorem absent_separation (point : context.base.Elements) :
    ((separate domain (StablePredicate.absent domain)).model point).carrier = ∅ :=
  PresentedType.restrict_false (domain.model point)

theorem absent_rows (point : context.base.Elements) :
    ((rows domain body (StablePredicate.absent body)).model point).carrier = ∅ := by
  apply HSet.eq_empty_iff.mpr
  intro value member
  obtain ⟨_, _, impossible, _⟩ := (mem_rows domain body (StablePredicate.absent body) point value).mp member
  exact impossible

end Controls

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualSeparationCollection
