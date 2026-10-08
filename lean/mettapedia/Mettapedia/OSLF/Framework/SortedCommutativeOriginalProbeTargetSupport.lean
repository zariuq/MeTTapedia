import Mettapedia.OSLF.Framework.SortedCommutativeOriginalProbeExclusion

/-!
# Every original probe successor retains the complete assay support

The original source redex and reactum both have zero fresh observer support.
The actual firing square and complete output equation therefore preserve
the whole input-plus-label support in the result. This holds even for
source unit rules, without assuming IPO exclusion or unique get results.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.Framework.SortedCommutativeInstruments.Source

open _root_.CategoryTheory
open Mettapedia.OSLF.SortedCommutative
open Mettapedia.GSLT.RedexRelativeCongruence
open Support

universe u

variable {Symbols : Type u} {arity : Symbols → Nat}

theorem mapped_step_support
    (sourceRules : ReactionRule (.origin : SourceCategory (arity := arity)) → Prop)
    {input output : ContextCategory arity}
    {agent : (.origin : ContextCategory arity) ⟶ input} {label : input ⟶ output}
    {result : (.origin : ContextCategory arity) ⟶ output}
    (step : ActIPO (mappedRules sourceRules) label agent result) :
    arrowObserverCount result = arrowObserverCount agent + arrowObserverCount label := by
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
    (sourceRules : ReactionRule (.origin : SourceCategory (arity := arity)) → Prop)
    (instrument : Probe arity)
    (supplied : SortedCommutativeInstruments.ValueClass arity
      (InstrumentCutContexts.receiver (sourceArity arity) instrument))
    (result : (.origin : ContextCategory arity) ⟶
      .interface (InstrumentCutContexts.result (sourceArity arity) instrument))
    (step : ActIPO (mappedRules sourceRules) (probeLabel instrument) (RawArrow.value supplied) result) :
    2 ≤ arrowObserverCount result := by
  rw [mapped_step_support sourceRules step, probeLabel_support]
  omega

end Mettapedia.OSLF.Framework.SortedCommutativeInstruments.Source
