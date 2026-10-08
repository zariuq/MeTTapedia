import Mettapedia.SetTheory.Profiles.ProfileGraphReadout
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphReceiptFamilies

/-!
# Dependent member consumers of the constructive graph readout

The target family retains a material member and its membership proposition.
The source family retains a literal child occurrence. Their comparison is
natural and sends complete compatible sections to complete compatible
sections. Its exact kernel is full future matching of the child values.

No inverse selects an occurrence from a material member. An arbitrary
dependent consumer crosses the quotient only with its proved section
compatibility; fibre equivalences without coherent transport do not suffice.
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.Profiles.ProfileGraphReadout

open CategoryTheory
open Mettapedia.TypeTheory.ContextualWitnessCover
open Mettapedia.TypeTheory.ContextualSmallFamilyUniverse
open Mettapedia.TypeTheory.MaterialSets.Hypersets
open ContextualGraphDiagrams ContextualRealizedGraphs

universe u v
variable (D : Type u) [Category.{u} D]

abbrev Support {point : D} (parent : Material D point) : Type (u+1) :=
  {child : Material D point // member D child parent}

def supportTransport {first second : D} (arrival : first ⟶ second)
    {parent : Material D first} (child : Support D parent) :
    Support D (transport D arrival parent) :=
  ⟨transport D arrival child.val, member_transport D arrival child.property⟩

def supportFamily : (materialValues D).Elements ⥤ Type (u+1) where
  obj point := Support D point.2
  map {first second} step := TypeCat.ofHom fun child =>
    ⟨transport D step.1 child.val, by
      have available := member_transport D step.1 child.property
      have same : transport D step.1 first.2 = second.2 := step.2
      exact Eq.mp (congrArg (fun parent : Material D second.1 =>
        member D (transport D step.1 child.val) parent) same) available⟩
  map_id point := by
    apply ConcreteCategory.hom_ext
    intro child
    exact Subtype.ext (transport_identity D point.1 child.val)
  map_comp earlier later := by
    apply ConcreteCategory.hom_ext
    intro child
    exact Subtype.ext (transport_composition D earlier.1 later.1 child.val)

/-- The original-small literal receipt family is compared with a
one-level-wider material support family. -/
def literalSupport (point : (values D).Elements)
    (child : (ContextualGraphReceiptFamilies.family D).obj point) :
    Support D (readout D point.2) :=
  ⟨readout D (childValue D point.2 child), ⟨Member.atChild point.2 child⟩⟩

theorem literalSupport_naturality {first second : (values D).Elements}
    (step : first ⟶ second) (child : (ContextualGraphReceiptFamilies.family D).obj first) :
    (supportFamily D).map ((elementMap (reading D)).map step) (literalSupport D first child) =
      literalSupport D second ((ContextualGraphReceiptFamilies.family D).map step child) := by
  apply Subtype.ext
  exact congrArg (readout D) (ContextualGraphReceiptFamilies.childValue_map D step child).symm

theorem literalSupport_kernel (point : (values D).Elements)
    (first second : (ContextualGraphReceiptFamilies.family D).obj point) :
    literalSupport D point first = literalSupport D point second ↔
      Nonempty (Equal (childValue D point.2 first) (childValue D point.2 second)) := by
  constructor
  · intro same
    exact (readout_kernel D _ _).mp (congrArg Subtype.val same)
  · intro same
    exact Subtype.ext ((readout_kernel D _ _).mpr same)

/-- Coverage proves that material members have literal presentations. It
does not select a source occurrence or a coherent inverse section. -/
theorem literalSupport_surjective (point : (values D).Elements) :
    Function.Surjective (literalSupport D point) := by
  rintro ⟨child, available⟩
  induction child using Quotient.inductionOn with
  | h child =>
    obtain ⟨proof⟩ := available
    refine ⟨proof.1, Subtype.ext ?_⟩
    exact (readout_kernel D _ _).mpr ⟨proof.2.symm⟩

def supportSection (term : (ContextualGraphReceiptFamilies.family D).sections) :
    (restrict.{u, u+1, u+1, u+1}
      (elementMap.{u, u+1, u+1} (reading D)) (supportFamily D)).sections :=
  ⟨fun point => literalSupport D point (term.val point), by
    intro first second step
    exact (literalSupport_naturality D step (term.val first)).trans
      (congrArg (literalSupport D second) (term.property step))⟩

theorem supportSection_computes (term : (ContextualGraphReceiptFamilies.family D).sections)
    (point : (values D).Elements) :
    (supportSection D term).val point = literalSupport D point (term.val point) := rfl

theorem supportSection_kernel
    (first second : (ContextualGraphReceiptFamilies.family D).sections) :
    supportSection D first = supportSection D second ↔
      ∀ point : (values D).Elements, Nonempty (Equal (childValue D point.2 (first.val point))
        (childValue D point.2 (second.val point))) := by
  constructor
  · intro same point
    exact (literalSupport_kernel D point _ _).mp
      (congrArg (fun term => term.val point) same)
  · intro same
    apply Subtype.ext
    funext point
    exact (literalSupport_kernel D point _ _).mpr (same point)

section AlongParent

variable {D} {base : D ⥤ Type v}
variable (parent : NaturalHom base (values D))

def supportAlong : base.Elements ⥤ Type (u+1) :=
  restrict (elementMap (parent.comp (reading D))) (supportFamily D)

def literalSupportAlong (point : base.Elements)
    (child : (ContextualGraphReceiptFamilies.along parent).obj point) :
    (supportAlong parent).obj point :=
  literalSupport D ((elementMap parent).obj point) child

theorem literalSupportAlong_naturality {first second : base.Elements}
    (step : first ⟶ second) (child : (ContextualGraphReceiptFamilies.along parent).obj first) :
    (supportAlong parent).map step (literalSupportAlong parent first child) =
      literalSupportAlong parent second ((ContextualGraphReceiptFamilies.along parent).map step child) :=
  literalSupport_naturality D ((elementMap parent).map step) child

def supportAlongSection (term : (ContextualGraphReceiptFamilies.along parent).sections) :
    (supportAlong parent).sections :=
  ⟨fun point => literalSupportAlong parent point (term.val point), by
    intro first second step
    exact (literalSupportAlong_naturality parent step (term.val first)).trans
      (congrArg (literalSupportAlong parent second) (term.property step))⟩

theorem supportAlongSection_value
    (term : (ContextualGraphReceiptFamilies.along parent).sections) (point : base.Elements) :
    ((supportAlongSection parent term).val point).val =
      readout D (childValue D (parent.app point.1 point.2) (term.val point)) := rfl

end AlongParent

section WholeDescent

variable {D}
variable (family : (materialValues D).Elements ⥤ Type v)

def pullbackFamily : (values D).Elements ⥤ Type v :=
  restrict.{u, v, u+1, u+1} (elementMap.{u, u+1, u+1} (reading D)) family

/-- Compatibility compares the values of an actual complete source
section, in their actual target-dependent fibres. -/
def SectionCompatible (term : (pullbackFamily family).sections) : Prop :=
  ∀ (point : D) (first second : Value D point), Nonempty (Equal first second) →
    HEq (term.val ⟨point, first⟩) (term.val ⟨point, second⟩)

def pullbackSection (term : family.sections) : (pullbackFamily family).sections :=
  ⟨fun point => term.val ((elementMap (reading D)).obj point),
    fun step => term.property ((elementMap (reading D)).map step)⟩

theorem pullbackSection_compatible (term : family.sections) :
    SectionCompatible family (pullbackSection family term) := by
  intro point first second matching
  have same : (⟨point, readout D first⟩ : (materialValues D).Elements) =
      ⟨point, readout D second⟩ := congrArg (fun value : Material D point =>
        (⟨point, value⟩ : (materialValues D).Elements))
        ((readout_kernel D first second).mpr matching)
  change HEq (term.val ⟨point, readout D first⟩) (term.val ⟨point, readout D second⟩)
  rw [same]

def descendSection (term : (pullbackFamily family).sections)
    (compatible : SectionCompatible family term) : family.sections :=
  ⟨fun point => Quotient.hrecOn (motive := fun material => family.obj ⟨point.1, material⟩) point.2
      (fun value => term.val ⟨point.1, value⟩) (compatible point.1), by
    intro first second step
    rcases first with ⟨first, firstValue⟩
    rcases second with ⟨second, secondValue⟩
    rcases step with ⟨arrival, arrives⟩
    change Material D first at firstValue
    change Material D second at secondValue
    change first ⟶ second at arrival
    change transport D arrival firstValue = secondValue at arrives
    subst secondValue
    induction firstValue using Quotient.inductionOn with
    | h firstValue =>
      exact term.property (CategoryOfElements.homMk (F := values D)
        ⟨first, firstValue⟩ ⟨second, move D arrival firstValue⟩ arrival rfl)⟩

theorem pullback_descendSection (term : (pullbackFamily family).sections)
    (compatible : SectionCompatible family term) :
    pullbackSection family (descendSection family term compatible) = term := by
  apply Subtype.ext
  rfl

theorem descend_pullbackSection (term : family.sections) :
    descendSection family (pullbackSection family term) (pullbackSection_compatible family term) = term := by
  apply Subtype.ext
  funext point
  rcases point with ⟨point, value⟩
  induction value using Quotient.inductionOn with
  | h value => rfl

/-- Necessity and sufficiency concern the full natural section, including
every context arrow, not just a list of independent current values. -/
theorem section_descends_iff (term : (pullbackFamily family).sections) :
    (∃ descended : family.sections, pullbackSection family descended = term) ↔
      SectionCompatible family term := by
  constructor
  · rintro ⟨descended, rfl⟩
    exact pullbackSection_compatible family descended
  · intro compatible
    exact ⟨descendSection family term compatible, pullback_descendSection family term compatible⟩

def compatibleSectionEquiv :
    {term : (pullbackFamily family).sections // SectionCompatible family term} ≃ family.sections where
  toFun term := descendSection family term.val term.property
  invFun term := ⟨pullbackSection family term, pullbackSection_compatible family term⟩
  left_inv term := Subtype.ext (pullback_descendSection family term.val term.property)
  right_inv := descend_pullbackSection family

end WholeDescent

end Mettapedia.SetTheory.Profiles.ProfileGraphReadout
