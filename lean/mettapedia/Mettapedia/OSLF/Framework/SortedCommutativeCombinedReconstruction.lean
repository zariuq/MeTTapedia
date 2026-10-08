import Mettapedia.OSLF.Framework.SortedCommutativeNativeProbeReadout
import Mettapedia.OSLF.Framework.SortedCommutativeOriginalProbeTargetSupport
import Mettapedia.OSLF.Framework.SortedCommutativeCombinedObserverSeparation

/-!
# Complete source reconstruction with arbitrary original rules

Original source rules may include unit redexes and may compete with get
probes. Every such original successor retains the fresh probe support. An
administrative successor reads the complete supplied native coordinate.
Structural induction reconstructs a matched successor before using its
earned purity to exclude the original alternative. Thus get results need
not be unique for complete future probes to recover a pure source class.

The right state is an arbitrary native value, including observer-bearing
values. No purity retraction, nonunit admission or structural observation
predicate is supplied. Origins are inhabited explicitly, and labels are
the actual literal categorical arrows of this typed first-order AC1 model.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.OSLF.Framework.SortedCommutativeInstruments

open _root_.CategoryTheory
open Mettapedia.OSLF.SortedCommutative
open Mettapedia.GSLT.RedexRelativeCongruence
open Support

universe u w

variable {Symbols : Type u} {arity : Symbols → Nat} {Origins : Type w}
variable (sourceRules : ReactionRule (.origin : Source.SourceCategory (arity := arity)) → Prop)

theorem combined_get_pure_result_readout (constructor : SourceSymbol Symbols)
    (arguments : Fin (sourceArity arity constructor) → Value arity .base)
    (position : Fin (sourceArity arity constructor)) (result : ValueClass arity .base)
    (pure : arrowObserverCount (RawArrow.value result :
      (.origin : ContextCategory arity) ⟶ .interface .base) = 0)
    (step : ActIPO (combinedSourceRules sourceRules Origins) (getLabel constructor position)
      (RawArrow.value (classOf (bundle arity constructor arguments))) (RawArrow.value result)) :
    Nonempty Origins ∧ result = classOf (arguments position) := by
  obtain ⟨rule, admitted, reaction, square, minimal, output⟩ := step
  rcases admitted with administrative | original
  · exact (get_native_step_iff constructor arguments position result).mp
      ⟨rule, administrative, reaction, square, minimal, output⟩
  · have bounded := Source.original_probe_result_is_not_pure sourceRules
      (.get constructor position) (classOf (bundle arity constructor arguments)) (RawArrow.value result)
      ⟨rule, original, reaction, square, minimal, output⟩
    omega

private theorem combined_constructor_reconstruction
    (origins : Nonempty Origins) (constructor : SourceSymbol Symbols)
    (arguments : Fin (sourceArity arity constructor) → Source.Value arity)
    (childRecovery : ∀ position (right : ValueClass arity .base),
      IPOBisimilar (combinedSourceRules sourceRules Origins)
        (RawArrow.value (classOf (Source.embed (arguments position)))) (RawArrow.value right) →
          classOf (Source.embed (arguments position)) = right)
    (right : ValueClass arity .base)
    (related : IPOBisimilar (combinedSourceRules sourceRules Origins)
      (RawArrow.value (classOf (Source.embed (Source.sourceNode constructor arguments))))
      (RawArrow.value right)) :
    classOf (Source.embed (Source.sourceNode constructor arguments)) = right := by
  obtain ⟨origin⟩ := origins
  let embedded := fun position => Source.embed (arguments position)
  have askStep : ActIPO (combinedSourceRules sourceRules Origins) (askLabel constructor)
      (RawArrow.value (classOf (Source.embed (Source.sourceNode constructor arguments))))
      (RawArrow.value (classOf (bundle arity constructor embedded))) :=
    (combined_ask_source_step_iff sourceRules constructor _ _).mpr ⟨origin, arguments, rfl, rfl⟩
  obtain ⟨matched, matchedStep, tupleRelated⟩ := ipoBisimilar_forward related askStep
  cases matched with
  | value matched =>
    have administrative := (combined_ask_step_iff_administrative
      sourceRules constructor right (RawArrow.value matched)).mp matchedStep
    obtain ⟨_matchedOrigin, before, rightRead, wholeTarget⟩ :=
      (ask_native_step_iff constructor right matched).mp administrative
    rw [wholeTarget] at tupleRelated
    have coordinates : ∀ position, classOf (embedded position) = classOf (before position) := by
      intro position
      have getStep : ActIPO (combinedSourceRules sourceRules Origins) (getLabel constructor position)
          (RawArrow.value (classOf (bundle arity constructor embedded)))
          (RawArrow.value (classOf (embedded position))) := by
        obtain ⟨rule, admitted, reaction, square, minimal, output⟩ :=
          (Occurrence.get origin constructor embedded position).direct_step
        exact ⟨rule, Or.inl admitted, reaction, square, minimal, output⟩
      obtain ⟨after, afterStep, childRelated⟩ := ipoBisimilar_forward tupleRelated getStep
      cases after with
      | value after =>
        have recovered : classOf (embedded position) = after := childRecovery position after childRelated
        have pureAfter : arrowObserverCount (RawArrow.value after :
            (.origin : ContextCategory arity) ⟶ .interface .base) = 0 := by
          rw [← recovered]
          exact classObserverCount_embedding (classOf (arguments position))
        have actualCoordinate := (combined_get_pure_result_readout sourceRules
          constructor before position after pureAfter afterStep).2
        exact recovered.trans actualCoordinate
    exact (congrArg classOf (Source.sourceNode_embed constructor arguments)).trans
      ((sourceNode_class_congruence constructor embedded before coordinates).trans rightRead.symm)

private theorem raw_source_combined_reconstruction
    (origins : Nonempty Origins) {sort : (Source.signature arity).Srt}
    (left : Term (Source.signature arity) (Source.Parallel arity) sort) :
    ∀ right : ValueClass arity .base, IPOBisimilar (combinedSourceRules sourceRules Origins)
      (RawArrow.value (classOf (Source.embed left))) (RawArrow.value right) →
      classOf (Source.embed left) = right := by
  apply @Term.rec (Source.signature arity) (Source.Parallel arity)
    (fun _ left => ∀ right : ValueClass arity .base,
      IPOBisimilar (combinedSourceRules sourceRules Origins)
        (RawArrow.value (classOf (Source.embed left))) (RawArrow.value right) →
          classOf (Source.embed left) = right) (t := left)
  · intro sort parallel right related
    exact combined_constructor_reconstruction sourceRules origins .unit
      (fun position => Fin.elim0 position) (fun position => Fin.elim0 position) right related
  · intro sort parallel first second firstInduction secondInduction right related
    change sort = ULift.up () at parallel
    subst sort
    let arguments : Fin 2 → Source.Value arity := Fin.cases first (fun _ => second)
    have recoveries : ∀ position (after : ValueClass arity .base),
        IPOBisimilar (combinedSourceRules sourceRules Origins)
          (RawArrow.value (classOf (Source.embed (arguments position)))) (RawArrow.value after) →
            classOf (Source.embed (arguments position)) = after := by
      intro position
      fin_cases position
      · exact firstInduction
      · exact secondInduction
    exact combined_constructor_reconstruction sourceRules origins .properCut arguments recoveries right related
  · intro constructor arguments inductionHypothesis right related
    exact combined_constructor_reconstruction sourceRules origins (.ordinary constructor)
      arguments inductionHypothesis right related

theorem combined_observer_bisimilar_iff_embedded_equal (origins : Nonempty Origins)
    (left : Source.ValueClass arity) (right : ValueClass arity .base) :
    IPOBisimilar (combinedSourceRules sourceRules Origins)
      (RawArrow.value (Source.classEmbedding left)) (RawArrow.value right) ↔
        Source.classEmbedding left = right := by
  constructor
  · refine Quotient.inductionOn left ?_
    intro raw related
    exact raw_source_combined_reconstruction sourceRules origins raw right related
  · intro same
    rw [same]
    exact ipoBisimilar_refl _ _

theorem combined_observer_bisimilar_iff_source_equal_all_rules (origins : Nonempty Origins)
    (first second : Source.ValueClass arity) :
    IPOBisimilar (combinedSourceRules sourceRules Origins)
      (RawArrow.value (Source.classEmbedding first)) (RawArrow.value (Source.classEmbedding second)) ↔
        first = second :=
  (combined_observer_bisimilar_iff_embedded_equal sourceRules origins first (Source.classEmbedding second)).trans
    ⟨fun same => Source.classEmbedding_injective same, fun same => congrArg Source.classEmbedding same⟩

theorem combined_observer_raw_bisimilar_iff_source_equation_all_rules (origins : Nonempty Origins)
    (first second : Source.Value arity) :
    IPOBisimilar (combinedSourceRules sourceRules Origins)
      (RawArrow.value (classOf (Source.embed first))) (RawArrow.value (classOf (Source.embed second))) ↔
        Equation first second :=
  (combined_observer_bisimilar_iff_source_equal_all_rules sourceRules origins (classOf first) (classOf second)).trans
    ⟨fun same => Quotient.exact same, fun equation => Quotient.sound equation⟩

end Mettapedia.OSLF.Framework.SortedCommutativeInstruments
