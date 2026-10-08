import Mettapedia.OSLF.Framework.SortedTypedInstrumentOriginalAskExclusion

/-!
# Complete original-successor support and conditional get recovery

Original source redexes and reacta have zero hereditary observer support.
Their actual firing equations therefore preserve the complete agent-plus-
label support in every native result, including for unit rules. A separately
earned pure matched result excludes that competing original alternative;
whole-family administrative get inversion then reads its exact coordinate.
Purity is not inferred from a current observation or chosen decoder.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.Framework.SortedTypedInstruments

open _root_.CategoryTheory
open Mettapedia.OSLF.SortedCommutative
open Mettapedia.GSLT.RedexRelativeCongruence

universe u v w

variable {source : Mettapedia.OSLF.SortedConstructors.Signature.{u,v}}
  {Parallel : source.Srt → Prop} {Origins : Type w}

namespace Source

theorem mapped_step_support
    (sourceRules : ReactionRule (.origin : SourceCategory source Parallel) → Prop)
    {input output : ContextCategory source Parallel}
    {agent : (.origin : ContextCategory source Parallel) ⟶ input} {label : input ⟶ output}
    {observed : (.origin : ContextCategory source Parallel) ⟶ output}
    (step : ActIPO (mappedRules sourceRules) label agent observed) :
    arrowObserverCount observed = arrowObserverCount agent + arrowObserverCount label := by
  obtain ⟨rule, ⟨original, _admitted, rfl⟩, reaction, square, _minimal, outputRead⟩ := step
  have redexPure : arrowObserverCount (mapReactionRule original).redex = 0 :=
    arrowObserverCount_embedding original.redex
  have reactumPure : arrowObserverCount (mapReactionRule original).reactum = 0 :=
    arrowObserverCount_embedding original.reactum
  have complete := congrArg arrowObserverCount square
  rw [arrowCount_comp, arrowCount_comp, redexPure, zero_add] at complete
  rw [outputRead, arrowCount_comp, reactumPure, zero_add]
  exact complete.symm

theorem original_probe_result_is_not_pure
    (sourceRules : ReactionRule (.origin : SourceCategory source Parallel) → Prop)
    (instrument : Probe source Parallel)
    (supplied : ValueClass (source := source) (Parallel := Parallel) (receiver instrument))
    (observed : (.origin : ContextCategory source Parallel) ⟶ .interface (result instrument))
    (step : ActIPO (mappedRules sourceRules) (probeLabel instrument) (RawArrow.value supplied) observed) :
    2 ≤ arrowObserverCount observed := by
  rw [mapped_step_support sourceRules step, probeLabel_support]
  omega

end Source

theorem combined_get_pure_result_readout
    (sourceRules : ReactionRule (.origin : SourceCategory source Parallel) → Prop)
    (head : SourceHead source Parallel) (arguments : Arguments head) (position : Fin (headArity head))
    (observed : ValueClass (source := source) (Parallel := Parallel) (.original (headInput head position)))
    (pure : classObserverCount observed = 0)
    (step : ActIPO (combinedSourceRules sourceRules Origins) (probeLabel (.get head position))
      (RawArrow.value (classOf (bundle head arguments))) (RawArrow.value observed)) :
    Nonempty Origins ∧ observed = classOf (arguments position) := by
  obtain ⟨rule, admitted, reaction, square, minimal, output⟩ := step
  rcases admitted with administrative | original
  · exact (get_bundle_step_iff head arguments position observed).mp
      ⟨rule, administrative, reaction, square, minimal, output⟩
  · have bounded := Source.original_probe_result_is_not_pure sourceRules
      (.get head position) (classOf (bundle head arguments)) (RawArrow.value observed)
      ⟨rule, original, reaction, square, minimal, output⟩
    change 2 ≤ classObserverCount observed at bounded
    omega

end Mettapedia.OSLF.Framework.SortedTypedInstruments
