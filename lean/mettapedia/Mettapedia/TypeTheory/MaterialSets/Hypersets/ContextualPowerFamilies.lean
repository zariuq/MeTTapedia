import Mettapedia.TypeTheory.MaterialSets.Hypersets.FuturePowerFamilies
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualSeparationCollection

/-!
# Material power families of full contextual predicates

Faithful labels of every future context, actual arrow and dependent argument
form one material set. Its powerset contains all future predicates;
separation retains precisely those stable under actual future restriction.
Membership of a retained label constructs the decoder, with both inverse
laws. No host context or arrow is decoded from a material label.

For an interpreted family with small context, arrows and argument fibres,
the power family remains at the same graph universe. The construction uses
full proposition-valued powerset and full separation. Arbitrary bare member
families first require the independently constructed successor-site model.
These are powerobjects of the interpreted displayed families, rather than
an internal small-powerclass on all large objects or an indexed final
coalgebra for such a powerclass.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualPowerFamilies

open CategoryTheory
open AccessiblePointedGraph
open ContextualGeneratedUniverse
open FuturePowerFamilies
open PowerClassPresheafBaseChange

universe u

namespace LabelSubsets

variable {I : Type u} (coding : ArgumentCoding I)

def labelsGraph : AccessiblePointedGraph.{u} := sup coding.graph

def subsetGraph (predicate : I → Prop) : AccessiblePointedGraph.{u} :=
  sup fun argument : {argument : I // predicate argument} => coding.graph argument.val

theorem mem_subsetGraph (predicate : I → Prop) (value : HSet.{u}) :
    value ∈ HSet.mk (subsetGraph coding predicate) ↔
      ∃ argument, predicate argument ∧ coding.reading argument = value := by
  change value ∈ HSet.range (fun argument : {argument : I // predicate argument} =>
    coding.graph argument.val) ↔ _
  rw [HSet.mem_range]
  constructor
  · rintro ⟨argument, same⟩
    exact ⟨argument.val, argument.property, same⟩
  · rintro ⟨argument, available, same⟩
    exact ⟨⟨argument, available⟩, same⟩

theorem label_mem_subsetGraph (predicate : I → Prop) (argument : I) :
    coding.reading argument ∈ HSet.mk (subsetGraph coding predicate) ↔ predicate argument := by
  rw [mem_subsetGraph]
  exact ⟨fun ⟨other, available, same⟩ => coding.injective same ▸ available,
    fun available => ⟨argument, available, rfl⟩⟩

def subsetsGraph : AccessiblePointedGraph.{u} := sup (subsetGraph coding)

theorem subsetGraph_subset (predicate : I → Prop) :
    HSet.mk (subsetGraph coding predicate) ⊆ HSet.mk (labelsGraph coding) := by
  intro value available
  obtain ⟨argument, _, same⟩ := (mem_subsetGraph coding predicate value).mp available
  exact HSet.mem_range.mpr ⟨argument, same⟩

/-- The graph range over the full predicate type is exactly the material
powerset of the faithfully labelled argument set. -/
theorem mk_subsetsGraph : HSet.mk (subsetsGraph coding) = HSet.powerset (HSet.mk (labelsGraph coding)) := by
  apply HSet.ext
  intro value
  change value ∈ HSet.range (LabelSubsets.subsetGraph coding) ↔ _
  rw [HSet.mem_range, HSet.mem_powerset]
  constructor
  · rintro ⟨predicate, rfl⟩
    exact subsetGraph_subset coding predicate
  · intro bounded
    refine ⟨fun argument => coding.reading argument ∈ value, ?_⟩
    apply HSet.ext
    intro entry
    rw [mem_subsetGraph]
    constructor
    · rintro ⟨argument, available, same⟩
      exact same ▸ available
    · intro available
      obtain ⟨argument, same⟩ := HSet.mem_range.mp (bounded available)
      change coding.reading argument = entry at same
      exact ⟨argument, same.symm ▸ available, same⟩

theorem recover_subset {value : HSet.{u}} (bounded : value ⊆ HSet.mk (labelsGraph coding)) :
    HSet.mk (subsetGraph coding (fun argument => coding.reading argument ∈ value)) = value := by
  apply HSet.ext
  intro entry
  rw [mem_subsetGraph]
  constructor
  · rintro ⟨argument, available, same⟩
    exact same ▸ available
  · intro available
    obtain ⟨argument, same⟩ := HSet.mem_range.mp (bounded available)
    change coding.reading argument = entry at same
    exact ⟨argument, same.symm ▸ available, same⟩

end LabelSubsets

variable {D : Type u} [Category.{u} D]
variable (A : D ⥤ Type u) (point : D) (coding : ArgumentCoding (Arguments A point))

def ClosedReading (value : HSet.{u}) : Prop :=
  ∀ {first second : Arguments A point} (_step : first ⟶ second),
    coding.reading first ∈ value → coding.reading second ∈ value

def predicateGraph : AccessiblePointedGraph.{u} :=
  separationGraph (LabelSubsets.subsetsGraph coding) (ClosedReading A point coding)

theorem mk_predicateGraph : HSet.mk (predicateGraph A point coding) =
    HSet.sep (ClosedReading A point coding)
      (HSet.powerset (HSet.mk (LabelSubsets.labelsGraph coding))) := by
  rw [predicateGraph, mk_separationGraph, LabelSubsets.mk_subsetsGraph]

def predicateValue (predicate : Predicate A point) : HSet.{u} :=
  HSet.mk (LabelSubsets.subsetGraph coding predicate.holds)

theorem predicateValue_entry (predicate : Predicate A point) (argument : Arguments A point) :
    coding.reading argument ∈ predicateValue A point coding predicate ↔ predicate.holds argument :=
  LabelSubsets.label_mem_subsetGraph coding predicate.holds argument

theorem predicateValue_mem (predicate : Predicate A point) :
    predicateValue A point coding predicate ∈ HSet.mk (predicateGraph A point coding) := by
  rw [mk_predicateGraph, HSet.mem_sep, HSet.mem_powerset]
  refine ⟨LabelSubsets.subsetGraph_subset coding predicate.holds, ?_⟩
  intro first second step available
  exact (predicateValue_entry A point coding predicate second).mpr
    (predicate.closed step ((predicateValue_entry A point coding predicate first).mp available))

def decodePredicate (member : {value : HSet.{u} // value ∈ HSet.mk (predicateGraph A point coding)}) :
    Predicate A point where
  holds argument := coding.reading argument ∈ member.val
  closed step available := by
    have represented : member.val ∈ HSet.sep (ClosedReading A point coding)
        (HSet.powerset (HSet.mk (LabelSubsets.labelsGraph coding))) := by
      rw [← mk_predicateGraph]
      exact member.property
    have stable : ClosedReading A point coding member.val := (HSet.mem_sep.mp represented).2
    exact stable step available

def encodePredicate (predicate : Predicate A point) :
    {value : HSet.{u} // value ∈ HSet.mk (predicateGraph A point coding)} :=
  ⟨predicateValue A point coding predicate, predicateValue_mem A point coding predicate⟩

theorem decode_encode (predicate : Predicate A point) :
    decodePredicate A point coding (encodePredicate A point coding predicate) = predicate := by
  apply Predicate.ext
  exact predicateValue_entry A point coding predicate

theorem encode_decode (member : {value : HSet.{u} // value ∈ HSet.mk (predicateGraph A point coding)}) :
    encodePredicate A point coding (decodePredicate A point coding member) = member := by
  apply Subtype.ext
  have represented : member.val ∈ HSet.sep (ClosedReading A point coding)
      (HSet.powerset (HSet.mk (LabelSubsets.labelsGraph coding))) := by
    rw [← mk_predicateGraph]
    exact member.property
  have bounded := HSet.mem_powerset.mp
    ((HSet.mem_sep.mp represented)).1
  exact LabelSubsets.recover_subset coding bounded

def predicateModel : PresentedType (Predicate A point) where
  graph := predicateGraph A point coding
  decode := {
    toFun := decodePredicate A point coding
    invFun := encodePredicate A point coding
    left_inv := encode_decode A point coding
    right_inv := decode_encode A point coding }

theorem predicateModel_value (predicate : Predicate A point) :
    (predicateModel A point coding).value predicate = predicateValue A point coding predicate := rfl

theorem predicateModel_carrier : (predicateModel A point coding).carrier =
    HSet.sep (ClosedReading A point coding)
      (HSet.powerset (HSet.mk (LabelSubsets.labelsGraph coding))) := mk_predicateGraph A point coding

theorem predicateModel_decode_truth
    (member : {value : HSet.{u} // value ∈ (predicateModel A point coding).carrier})
    (argument : Arguments A point) :
    ((predicateModel A point coding).decode member).holds argument ↔ coding.reading argument ∈ member.val := Iff.rfl

variable {C : Type u} [Category.{u} C] {context : LabelledContext C}
variable (domain : MaterialFamily context)
variable (arrows : (first second : Cᵒᵖ) → ArgumentCoding (first ⟶ second))

/-- The material carrier and every decoder are constructed from the domain's
faithful context, actual-arrow and term graph dictionaries. -/
def power : MaterialFamily context where
  family := family domain.family
  model point := predicateModel domain.family point (domain.futureCoding arrows point)

theorem power_carrier (point : context.base.Elements) :
    ((power domain arrows).model point).carrier =
      HSet.sep (ClosedReading domain.family point (domain.futureCoding arrows point))
        (HSet.powerset (HSet.mk (LabelSubsets.labelsGraph (domain.futureCoding arrows point)))) :=
  predicateModel_carrier domain.family point (domain.futureCoding arrows point)

theorem power_truth (point : context.base.Elements) (predicate : (power domain arrows).family.obj point)
    (argument : Arguments domain.family point) :
    (domain.futureCoding arrows point).reading argument ∈ ((power domain arrows).model point).value predicate ↔
      predicate.holds argument := predicateValue_entry _ _ _ _ _

/-- Restriction changes the full future index before testing membership. It
does not use only the present target or transported present argument. -/
theorem power_restriction_truth {first second : context.base.Elements} (step : first ⟶ second)
    (predicate : (power domain arrows).family.obj first) (argument : Arguments domain.family second) :
    (domain.futureCoding arrows second).reading argument ∈
      ((power domain arrows).model second).value ((power domain arrows).family.map step predicate) ↔
    (domain.futureCoding arrows first).reading ((futurePrecompose domain.family step).obj argument) ∈
      ((power domain arrows).model first).value predicate := by
  rw [power_truth, power_truth]
  exact Iff.rfl

def stablePredicateEquiv : ContextualSeparationCollection.StablePredicate domain ≃
    FuturePowerFamilies.StablePredicate domain.family where
  toFun predicate := {
    holds argument := predicate.holds argument.1 argument.2
    closed {first second} step available := by
      have transported := predicate.map step.1 first.2 available
      exact step.2 ▸ transported }
  invFun predicate := {
    holds point argument := predicate.holds ⟨point, argument⟩
    map step argument available := predicate.closed
      (CategoryOfElements.homMk _ _ step rfl) available }
  left_inv predicate := by
    cases predicate
    rfl
  right_inv predicate := by
    apply FuturePowerFamilies.StablePredicate.ext
    intro argument
    exact Iff.rfl

/-- Every stable displayed subset determines a natural material power
section, and every such section recovers precisely that subset. -/
def classifierEquiv : ContextualSeparationCollection.StablePredicate domain ≃
    (power domain arrows).family.sections :=
  (stablePredicateEquiv domain).trans (FuturePowerFamilies.classifierEquiv domain.family)

theorem classifier_truth (predicate : ContextualSeparationCollection.StablePredicate domain)
    (point : context.base.Elements) (argument : Arguments domain.family point) :
    (domain.futureCoding arrows point).reading argument ∈
      ((power domain arrows).model point).value ((classifierEquiv domain arrows predicate).val point) ↔
      predicate.holds argument.1.1 argument.2 := by
  rw [power_truth]
  exact Iff.rfl

/-- The present material subset is an observation of a power-family
element. It does not retain truth at every future argument. -/
def presentPart (point : context.base.Elements) (predicate : (power domain arrows).family.obj point) : HSet.{u} :=
  HSet.sep (fun value => ∃ argument, (domain.model point).value argument = value ∧
    predicate.holds (current domain.family point argument)) (domain.model point).carrier

theorem mem_presentPart (point : context.base.Elements)
    (predicate : (power domain arrows).family.obj point) (value : HSet.{u}) :
    value ∈ presentPart domain arrows point predicate ↔
      ∃ argument, (domain.model point).value argument = value ∧
        predicate.holds (current domain.family point argument) := by
  rw [presentPart, HSet.mem_sep]
  constructor
  · exact And.right
  · rintro ⟨argument, same, available⟩
    exact ⟨same ▸ (domain.model point).value_mem argument, argument, same, available⟩

theorem presentPart_truth (point : context.base.Elements)
    (predicate : (power domain arrows).family.obj point) (argument : domain.family.obj point) :
    (domain.model point).value argument ∈ presentPart domain arrows point predicate ↔
      predicate.holds (current domain.family point argument) := by
  rw [mem_presentPart]
  constructor
  · rintro ⟨other, same, available⟩
    exact (domain.model point).value_injective same ▸ available
  · intro available
    exact ⟨argument, rfl, available⟩

/-- The current observation of the classifier section is the actual
separated material carrier supplied by contextual separation. -/
theorem classifier_presentPart (predicate : ContextualSeparationCollection.StablePredicate domain)
    (point : context.base.Elements) :
    presentPart domain arrows point ((classifierEquiv domain arrows predicate).val point) =
      ((ContextualSeparationCollection.separate domain predicate).model point).carrier := by
  apply HSet.ext
  intro value
  rw [mem_presentPart, ContextualSeparationCollection.mem_separated_carrier]
  constructor
  · rintro ⟨argument, same, available⟩
    exact ⟨argument, available, same⟩
  · rintro ⟨argument, available, same⟩
    exact ⟨argument, same, available⟩

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualPowerFamilies
