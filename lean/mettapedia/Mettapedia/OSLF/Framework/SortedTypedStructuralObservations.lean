import Mettapedia.OSLF.Framework.SortedTypedInstrumentPayloadReconstruction

/-!
# Independently defined typed structural observations

Structural formulas have a connective for each declared constructor, proper
designated Cut and unit. Satisfaction quantifies complete equation-class
decompositions at the actual input sorts. It is defined independently of
the administrative transition system and of any characteristic formula.

The characteristic formula of a supplied closed source term separates its
whole AC1 class, including unit and cross-root representatives. This earns
the logical comparison to payload-sensitive observer bisimilarity in the
closed first-order designated-AC1 grammar. No additional authored equation,
binder or reflective RUN congruence is admitted by this construction.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.OSLF.Framework.SortedTypedInstruments.StructuralObservations

open Mettapedia.OSLF.SortedCommutative
open Mettapedia.GSLT.RedexRelativeCongruence

universe u v w

variable {source : Mettapedia.OSLF.SortedConstructors.Signature.{u,v}}
  {Parallel : source.Srt → Prop}

inductive Formula (source : Mettapedia.OSLF.SortedConstructors.Signature.{u,v})
    (Parallel : source.Srt → Prop) : source.Srt → Type (max u v) where
  | unit {sort} (parallel : Parallel sort) : Formula source Parallel sort
  | cut {sort} (parallel : Parallel sort) (first second : Formula source Parallel sort) :
      Formula source Parallel sort
  | node (constructor : source.Constructor)
      (arguments : (position : Fin (source.arity constructor)) → Formula source Parallel (source.input constructor position)) :
      Formula source Parallel (source.output constructor)

def Holds : {sort : source.Srt} → Formula source Parallel sort → Class source Parallel sort → Prop
  | _, .unit parallel, supplied => supplied = classOf (.zero parallel)
  | _, .cut parallel first second, supplied =>
      ∃ left right : Class source Parallel _, supplied = classCut parallel left right ∧
        Holds first left ∧ Holds second right
  | _, .node constructor arguments, supplied =>
      ∃ children : (position : Fin (source.arity constructor)) → Class source Parallel (source.input constructor position),
        supplied = (Head.node constructor children).class ∧ ∀ position, Holds (arguments position) (children position)

def characteristic : {sort : source.Srt} → Term source Parallel sort → Formula source Parallel sort
  | _, .zero parallel => .unit parallel
  | _, .cut parallel first second => .cut parallel (characteristic first) (characteristic second)
  | _, .node constructor arguments => .node constructor (fun position => characteristic (arguments position))

theorem characteristic_holds_iff {sort : source.Srt} (term : Term source Parallel sort)
    (supplied : Class source Parallel sort) : Holds (characteristic term) supplied ↔ supplied = classOf term := by
  induction term with
  | zero parallel => rfl
  | cut parallel first second firstInduction secondInduction =>
    constructor
    · rintro ⟨left, right, whole, leftHolds, rightHolds⟩
      have leftRead := (firstInduction left).mp leftHolds
      have rightRead := (secondInduction right).mp rightHolds
      rw [leftRead, rightRead] at whole
      exact whole
    · intro whole
      exact ⟨classOf first, classOf second, whole,
        (firstInduction _).mpr rfl, (secondInduction _).mpr rfl⟩
  | node constructor arguments inductionHypothesis =>
    constructor
    · rintro ⟨children, whole, satisfies⟩
      have coordinates : children = fun position => classOf (arguments position) :=
        funext (fun position => (inductionHypothesis position (children position)).mp (satisfies position))
      rw [coordinates] at whole
      exact whole.trans (Head.class_node constructor arguments)
    · intro whole
      exact ⟨fun position => classOf (arguments position),
        whole.trans (Head.class_node constructor arguments).symm,
        fun position => (inductionHypothesis position _).mpr rfl⟩

def LogicalEquivalent {sort : source.Srt} (first second : Class source Parallel sort) : Prop :=
  ∀ formula : Formula source Parallel sort, Holds formula first ↔ Holds formula second

theorem logicalEquivalent_iff_equal {sort : source.Srt} (first second : Class source Parallel sort) :
    LogicalEquivalent first second ↔ first = second := by
  constructor
  · intro equivalent
    have firstHolds : Holds (characteristic first.out) first :=
      (characteristic_holds_iff first.out first).mpr (Quotient.out_eq first).symm
    have secondHolds := (equivalent (characteristic first.out)).mp firstHolds
    exact (Quotient.out_eq first).symm.trans
      ((characteristic_holds_iff first.out second).mp secondHolds).symm
  · rintro rfl
    exact fun _ => Iff.rfl

theorem logicalEquivalent_iff_payloadObserver_bisimilar {sort : source.Srt} {Origins : Type w}
    (sourceRules : ReactionRule (.origin : SourceCategory source Parallel) → Prop)
    (origins : Nonempty Origins) (first second : Class source Parallel sort) :
    LogicalEquivalent first second ↔
      (PayloadLabels.firingSystem (combinedSourceRules sourceRules Origins)).Bisimilar _
        (classEmbedding first) (classEmbedding second) :=
  (logicalEquivalent_iff_equal first second).trans
    (PayloadLabels.bisimilar_iff_source_equal sourceRules origins first second).symm

theorem raw_characteristic_observation_is_an_actual_equation_test {sort : source.Srt}
    (first second : Term source Parallel sort) :
    Holds (characteristic first) (classOf second) ↔ Equation first second :=
  (characteristic_holds_iff first (classOf second)).trans
    ⟨fun same => (Quotient.exact same).symm, fun equation => Quotient.sound equation.symm⟩

end Mettapedia.OSLF.Framework.SortedTypedInstruments.StructuralObservations
