import Mettapedia.OSLF.Framework.SortedCommutativeProbeReconstructionReadout

/-!
# Actual full-instrument IPO separation of source equation classes

The complete administrative family distinguishes precisely the independently
generated source AC1 classes. Ask recovers an actual matched source tuple;
the subsequent get transitions relate every complete coordinate. Raw-source
induction then reconstructs the whole source class against any right-hand
representative. No root decoder or structural equality observation is a
field of the bisimulation.

The result is restricted to this actual administrative reaction family and
requires inhabited receipt origins. Adding independently supplied source
reactions needs a separate IPO competition argument; it is not inferred
from these protocol inversions.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.OSLF.Framework.SortedCommutativeInstruments

open _root_.CategoryTheory
open Mettapedia.OSLF.SortedCommutative
open Mettapedia.GSLT.RedexRelativeCongruence

universe u w

variable {Symbols : Type u} {arity : Symbols → Nat} {Origins : Type w}

theorem full_observer_constructor_arguments
    (origins : Nonempty Origins) (constructor : SourceSymbol Symbols)
    (arguments : Fin (sourceArity arity constructor) → Source.Value arity)
    (right : Source.ValueClass arity)
    (related : IPOBisimilar (rules arity Origins)
      (RawArrow.value (Source.classEmbedding (classOf (Source.sourceNode constructor arguments))))
      (RawArrow.value (Source.classEmbedding right))) :
    ∃ before : Fin (sourceArity arity constructor) → Source.Value arity,
      right = classOf (Source.sourceNode constructor before) ∧
      ∀ position, IPOBisimilar (rules arity Origins)
        (RawArrow.value (Source.classEmbedding (classOf (arguments position))))
        (RawArrow.value (Source.classEmbedding (classOf (before position)))) := by
  obtain ⟨origin⟩ := origins
  have askStep : ActIPO (rules arity Origins) (askLabel constructor)
      (RawArrow.value (Source.classEmbedding (classOf (Source.sourceNode constructor arguments))))
      (RawArrow.value (sourceBundle constructor arguments)) :=
    (ask_source_step_iff constructor _ _).mpr ⟨origin, arguments, rfl, rfl⟩
  obtain ⟨matched, matchedStep, tupleRelated⟩ := ipoBisimilar_forward related askStep
  obtain ⟨_matchedOrigin, before, rightRead, wholeTarget⟩ :=
    (ask_source_step_iff constructor right matched).mp matchedStep
  rw [wholeTarget] at tupleRelated
  refine ⟨before, rightRead, ?_⟩
  intro position
  have getStep : ActIPO (rules arity Origins) (getLabel constructor position)
      (RawArrow.value (sourceBundle constructor arguments))
      (RawArrow.value (Source.classEmbedding (classOf (arguments position)))) :=
    (get_source_step_iff constructor arguments position _).mpr ⟨⟨origin⟩, rfl⟩
  obtain ⟨after, afterStep, childRelated⟩ := ipoBisimilar_forward tupleRelated getStep
  have childRead := ((get_source_step_iff constructor before position after).mp afterStep).2
  rw [childRead] at childRelated
  exact childRelated

private theorem raw_source_full_observer_separation
    (origins : Nonempty Origins) {sort : (Source.signature arity).Srt}
    (left : Term (Source.signature arity) (Source.Parallel arity) sort) :
    ∀ right : Source.ValueClass arity, IPOBisimilar (rules arity Origins)
      (RawArrow.value (classOf (Source.embed left)))
      (RawArrow.value (Source.classEmbedding right)) →
      classOf (Source.embed left) = Source.classEmbedding right := by
  apply @Term.rec (Source.signature arity) (Source.Parallel arity)
    (fun _ left => ∀ right : Source.ValueClass arity, IPOBisimilar (rules arity Origins)
      (RawArrow.value (classOf (Source.embed left)))
      (RawArrow.value (Source.classEmbedding right)) →
      classOf (Source.embed left) = Source.classEmbedding right) (t := left)
  · intro sort parallel right related
    obtain ⟨before, rightRead, _children⟩ := full_observer_constructor_arguments origins .unit
      (fun position => Fin.elim0 position) right related
    exact congrArg Source.classEmbedding rightRead.symm
  · intro sort parallel first second firstInduction secondInduction right related
    change sort = ULift.up () at parallel
    subst sort
    let arguments : Fin 2 → Source.Value arity := Fin.cases first (fun _ => second)
    obtain ⟨before, rightRead, children⟩ :=
      full_observer_constructor_arguments origins .properCut arguments right related
    have firstRead : classOf first = classOf (before 0) :=
      Source.classEmbedding_injective (firstInduction _ (children 0))
    have secondRead : classOf second = classOf (before 1) :=
      Source.classEmbedding_injective (secondInduction _ (children 1))
    have constructorRead : classOf (.cut rfl first second : Source.Value arity) =
        classOf (Source.sourceNode .properCut before) :=
      Quotient.sound (Equation.cut rfl (Quotient.exact firstRead) (Quotient.exact secondRead))
    exact congrArg Source.classEmbedding (constructorRead.trans rightRead.symm)
  · intro constructor arguments inductionHypothesis right related
    obtain ⟨before, rightRead, children⟩ :=
      full_observer_constructor_arguments origins (.ordinary constructor) arguments right related
    have coordinates : ∀ position, classOf (arguments position) = classOf (before position) :=
      fun position => Source.classEmbedding_injective (inductionHypothesis position _ (children position))
    have constructorRead := (node_class_eq_iff (signature := Source.signature arity)
      (Parallel := Source.Parallel arity) constructor arguments before).mpr coordinates
    exact congrArg Source.classEmbedding (constructorRead.trans rightRead.symm)

theorem full_observer_bisimilar_iff_source_equal (origins : Nonempty Origins)
    (first second : Source.ValueClass arity) :
    IPOBisimilar (rules arity Origins)
      (RawArrow.value (Source.classEmbedding first))
      (RawArrow.value (Source.classEmbedding second)) ↔ first = second := by
  constructor
  · revert first
    intro first
    refine Quotient.inductionOn first ?_
    intro raw related
    exact Source.classEmbedding_injective (raw_source_full_observer_separation origins raw second related)
  · intro same
    subst second
    exact ipoBisimilar_refl _ _

theorem full_observer_raw_bisimilar_iff_source_equation (origins : Nonempty Origins)
    (first second : Source.Value arity) :
    IPOBisimilar (rules arity Origins)
      (RawArrow.value (classOf (Source.embed first)))
      (RawArrow.value (classOf (Source.embed second))) ↔ Equation first second :=
  (full_observer_bisimilar_iff_source_equal origins (classOf first) (classOf second)).trans
    ⟨fun same => Quotient.exact same, fun equation => Quotient.sound equation⟩

end Mettapedia.OSLF.Framework.SortedCommutativeInstruments
