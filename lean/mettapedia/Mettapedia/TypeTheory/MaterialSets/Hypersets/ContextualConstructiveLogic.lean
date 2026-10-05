import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualSeparationCollection
import Mettapedia.GSLT.Logic.ObservedGeneratedModelControls

/-!
# Constructive propositions in the observed material-family model

Stable propositions are interpreted by constructed separated unit families.
Their negations are the actual all-future dependent products into the empty
family. The exact fibre criterion retains every context arrow. It differs
from simply negating present support.

On the infinite labelled-history model, positive history length is false
initially and inhabited after an extension. Its full future negation is
empty everywhere, while its double negation has an actual natural section.
This gives a non-Boolean internal control without adopting excluded middle,
choice, or double-negation elimination in the host construction.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualConstructiveLogic

open _root_.CategoryTheory ContextualGeneratedUniverse ContextualSeparationCollection
open Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent

universe u
section General
variable {C : Type u} [Category.{u} C]
variable {context : LabelledContext C}

structure StableProposition (context : LabelledContext C) where
  holds : context.base.Elements → Prop
  map : ∀ {first second : context.base.Elements} (_arrow : first ⟶ second),
    holds first → holds second

namespace StableProposition

variable (predicate : StableProposition context)

def onUnit : StablePredicate (MaterialFamily.unit context) where
  holds point _ := predicate.holds point
  map arrow _ proof := predicate.map arrow proof

def family : MaterialFamily context :=
  separate (MaterialFamily.unit context) predicate.onUnit

theorem fibre_inhabited_iff (point : context.base.Elements) :
    Nonempty (predicate.family.family.obj point) ↔ predicate.holds point := by
  constructor
  · rintro ⟨member⟩
    exact member.property
  · intro proof
    exact ⟨⟨⟨PUnit.unit⟩, proof⟩⟩

theorem present_value (point : context.base.Elements)
    (member : predicate.family.family.obj point) :
    (predicate.family.model point).value member = ∅ := by
  cases member.val with
  | up value => cases value; rfl

end StableProposition

variable (domain : MaterialFamily context)
variable (arrows : (first second : Cᵒᵖ) → ArgumentCoding (first ⟶ second))

def negation : MaterialFamily context :=
  domain.pi (MaterialFamily.empty domain.extension) arrows

/-- Exact intuitionistic negation in the actual future-dependent product. -/
theorem negation_fibre_iff (point : context.base.Elements) :
    Nonempty ((negation domain arrows).family.obj point) ↔
      ∀ (future : context.base.Elements), (point ⟶ future) →
        ¬ Nonempty (domain.family.obj future) := by
  constructor
  · rintro ⟨function⟩ future step ⟨argument⟩
    exact (function.app future step argument).down.elim
  · intro emptyAt
    exact ⟨{
      app := fun future step argument => (emptyAt future step ⟨argument⟩).elim
      naturality := by
        intro first second step restriction argument
        exact (emptyAt first restriction ⟨argument⟩).elim }⟩

theorem future_inhabited_excludes_negation {point future : context.base.Elements}
    (step : point ⟶ future) (member : domain.family.obj future) :
    ¬ Nonempty ((negation domain arrows).family.obj point) := by
  intro inhabited
  exact (negation_fibre_iff domain arrows point).mp inhabited future step ⟨member⟩

theorem carrier_empty_iff (point : context.base.Elements) :
    (domain.model point).carrier = ∅ ↔ ¬ Nonempty (domain.family.obj point) := by
  constructor
  · intro emptyCarrier ⟨term⟩
    have member := (domain.model point).value_mem term
    rw [emptyCarrier] at member
    exact HSet.notMem_empty _ member
  · intro noTerm
    apply HSet.ext
    intro value
    constructor
    · intro member
      exact (noTerm ⟨(domain.model point).decode ⟨value, member⟩⟩).elim
    · intro member
      exact (HSet.notMem_empty _ member).elim

/-- With no possible future arguments, a full function still exists and has
the empty material graph. Its family decoder is the usual Pi decoder. -/
theorem negation_value_empty (point : context.base.Elements)
    (emptyAt : ∀ (future : context.base.Elements), (point ⟶ future) →
      ¬ Nonempty (domain.family.obj future))
    (function : (negation domain arrows).family.obj point) :
    ((negation domain arrows).model point).value function = ∅ := by
  change HSet.mk (LabelledDependentProducts.functionGraph
    (domain.futureCoding arrows point)
    (domain.futureOutputs (MaterialFamily.empty domain.extension) point)
    (fun argument => function.app argument.1.1 argument.1.2 argument.2)) = ∅
  apply HSet.ext
  intro value
  constructor
  · intro member
    obtain ⟨argument, _⟩ := (LabelledDependentProducts.mem_functionGraph_iff
      (domain.futureCoding arrows point)
      (domain.futureOutputs (MaterialFamily.empty domain.extension) point)
      (fun argument => function.app argument.1.1 argument.1.2 argument.2) value).mp member
    exact (emptyAt argument.1.1 argument.1.2 ⟨argument.2⟩).elim
  · intro member
    exact (HSet.notMem_empty _ member).elim

variable (noNegative : ∀ point, ¬ Nonempty ((negation domain arrows).family.obj point))

/-- The section is built by abstraction over the proved empty negation
family. No pointwise witness or natural section is chosen. -/
def doubleNegationSection : (negation (negation domain arrows) arrows).family.sections :=
  PowerClassPresheafProducts.piLambda
    (⟨fun point => (noNegative ⟨point.1, point.2.1⟩ ⟨point.2.2⟩).elim, by
      intro first second step
      exact (noNegative ⟨first.1, first.2.1⟩ ⟨first.2.2⟩).elim⟩ :
      (MaterialFamily.empty (negation domain arrows).extension).family.sections)

theorem doubleNegationSection_value (point : context.base.Elements) :
    ((negation (negation domain arrows) arrows).model point).value
      ((doubleNegationSection domain arrows noNegative).val point) = ∅ :=
  negation_value_empty (negation domain arrows) arrows point
    (fun future _ => noNegative future) _

include noNegative in
theorem doubleNegation_carrier (point : context.base.Elements) :
    ((negation (negation domain arrows) arrows).model point).carrier = {∅} := by
  apply HSet.ext
  intro value
  rw [HSet.mem_singleton]
  constructor
  · intro member
    let decoded := ((negation (negation domain arrows) arrows).model point).decode ⟨value, member⟩
    exact (PresentedType.value_decode _ ⟨value, member⟩).symm.trans
      (negation_value_empty (negation domain arrows) arrows point
        (fun future _ => noNegative future) decoded)
  · intro same
    rw [same]
    have represented := ((negation (negation domain arrows) arrows).model point).value_mem
      ((doubleNegationSection domain arrows noNegative).val point)
    rw [doubleNegationSection_value] at represented
    exact represented

end General

namespace LabelledHistory

open Mettapedia.GSLT.ObservedGeneratedModelControls.Paths
open Mettapedia.GSLT.ObservedGeneratedModel

abbrev actualContext : LabelledContext Site :=
  Mettapedia.GSLT.ObservedGeneratedModel.context model worldCoding

def positive : StableProposition actualContext where
  holds point := 0 < point.1.unop.unop.length
  map {first second} step proof := by
    exact Nat.lt_of_lt_of_le proof
      ((Nat.le_add_right first.1.unop.unop.length step.val.unop.unop.val.length).trans_eq
        step.val.unop.unop.property)

def proposition : MaterialFamily actualContext := positive.family

def extendWorld (point : actualContext.base.Elements) : Siteᵒᵖ :=
  Opposite.op (Opposite.op ⟨point.1.unop.unop.length + 1⟩)

def extendStep (point : actualContext.base.Elements) : point.1 ⟶ extendWorld point :=
  (show point.1.unop.unop ⟶ (extendWorld point).unop.unop from ⟨[0], rfl⟩).op.op

def extended (point : actualContext.base.Elements) : actualContext.base.Elements :=
  ⟨extendWorld point, actualContext.base.map (extendStep point) point.2⟩

def extensionArrow (point : actualContext.base.Elements) : point ⟶ extended point :=
  ⟨extendStep point, rfl⟩

def futureMember (point : actualContext.base.Elements) : proposition.family.obj (extended point) :=
  ⟨⟨PUnit.unit⟩, Nat.zero_lt_succ point.1.unop.unop.length⟩

def initialPoint : actualContext.base.Elements := observedPoint model worldCoding oldRaw

theorem initial_fibre_empty : ¬ Nonempty (proposition.family.obj initialPoint) := by
  rintro ⟨member⟩
  exact Nat.not_lt_zero 0 member.property

theorem initial_carrier : (proposition.model initialPoint).carrier = ∅ :=
  (carrier_empty_iff proposition initialPoint).mpr initial_fibre_empty

theorem extension_fibre_inhabited (point : actualContext.base.Elements) :
    Nonempty (proposition.family.obj (extended point)) := ⟨futureMember point⟩

theorem extension_carrier (point : actualContext.base.Elements) :
    (proposition.model (extended point)).carrier = {∅} := by
  apply HSet.ext
  intro value
  rw [HSet.mem_singleton]
  constructor
  · intro member
    exact (PresentedType.value_decode _ ⟨value, member⟩).symm.trans
      (positive.present_value (extended point)
        ((proposition.model (extended point)).decode ⟨value, member⟩))
  · intro same
    rw [same]
    have represented := (proposition.model (extended point)).value_mem (futureMember point)
    exact (congrArg (fun reading : HSet => reading ∈ (proposition.model (extended point)).carrier)
      (positive.present_value (extended point) (futureMember point))).mp represented

theorem proposition_genuinely_varies :
    (proposition.model initialPoint).carrier ≠ (proposition.model (extended initialPoint)).carrier := by
  rw [initial_carrier, extension_carrier]
  intro same
  have member : (∅ : HSet) ∈ ({∅} : HSet) := HSet.mem_singleton.mpr rfl
  rw [← same] at member
  exact HSet.notMem_empty _ member

theorem proposition_has_no_global_section : ¬ Nonempty proposition.family.sections := by
  rintro ⟨term⟩
  exact initial_fibre_empty ⟨term.val initialPoint⟩

theorem no_negative_fibre (point : actualContext.base.Elements) :
    ¬ Nonempty ((negation proposition arrowCoding).family.obj point) :=
  future_inhabited_excludes_negation proposition arrowCoding (extensionArrow point) (futureMember point)

theorem negative_carrier (point : actualContext.base.Elements) :
    ((negation proposition arrowCoding).model point).carrier = ∅ :=
  (carrier_empty_iff (negation proposition arrowCoding) point).mpr (no_negative_fibre point)

def doubleNegativeSection : (negation (negation proposition arrowCoding) arrowCoding).family.sections :=
  doubleNegationSection proposition arrowCoding no_negative_fibre

theorem double_negative_carrier (point : actualContext.base.Elements) :
    ((negation (negation proposition arrowCoding) arrowCoding).model point).carrier = {∅} :=
  doubleNegation_carrier proposition arrowCoding no_negative_fibre point

theorem excluded_middle_has_no_initial_evidence :
    ¬ (Nonempty (proposition.family.obj initialPoint) ∨
      Nonempty ((negation proposition arrowCoding).family.obj initialPoint)) := by
  intro disjunction
  exact disjunction.elim initial_fibre_empty (no_negative_fibre initialPoint)

theorem no_double_negation_elimination :
    ¬ Nonempty (NatTrans (negation (negation proposition arrowCoding) arrowCoding).family
      proposition.family) := by
  rintro ⟨operation⟩
  exact initial_fibre_empty ⟨operation.app initialPoint (doubleNegativeSection.val initialPoint)⟩

theorem double_negation_not_present_support :
    Nonempty ((negation (negation proposition arrowCoding) arrowCoding).family.obj initialPoint) ∧
      ¬ Nonempty (proposition.family.obj initialPoint) :=
  ⟨⟨doubleNegativeSection.val initialPoint⟩, initial_fibre_empty⟩

end LabelledHistory

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualConstructiveLogic
