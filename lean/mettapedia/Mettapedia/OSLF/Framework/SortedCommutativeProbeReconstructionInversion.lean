import Mettapedia.OSLF.Framework.SortedCommutativeProbeReactionContexts
import Mettapedia.OSLF.Framework.SortedCommutativeProbeSourceReadout

/-!
# Whole-family reconstruction of complete three-head assays

An actual administrative IPO whose whole input has support three and erases
to the source unit must be a get or build declaration in the identity
reaction context. All matched arguments have hereditary support zero and
are reconstructed as actual source terms. The conclusion retains the
supplied origin, every argument and the whole result. Minimality is supplied
by the inspected actual firing; it is not inferred from matching alone.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.OSLF.Framework.SortedCommutativeInstruments

open _root_.CategoryTheory
open Mettapedia.OSLF.SortedCommutative
open Mettapedia.GSLT.RedexRelativeCongruence
open Support
open scoped BigOperators

universe u w

variable {Symbols : Type u} {arity : Symbols → Nat} {Origins : Type w}

theorem three_head_assay_inversion {inputSort : Srt arity}
    (supplied : ValueClass arity inputSort)
    (label : ContextClass (signature arity) (Parallel arity) inputSort .base)
    (result : (.origin : ContextCategory arity) ⟶ .interface .base)
    (completeSupport : classObserverCount (label.fill supplied) = 3)
    (erasedInput : Source.classRetraction (label.fill supplied) =
      classOf (.zero rfl : Source.Value arity))
    (step : ActIPO (rules arity Origins) (RawArrow.context label) (RawArrow.value supplied) result) :
    ∃ _suppliedOrigin : Origins, ∃ constructor : SourceSymbol Symbols,
      ∃ arguments : Fin (sourceArity arity constructor) → Source.Value arity,
        (∃ position : Fin (sourceArity arity constructor),
          label.fill supplied = classOf (cut arity (.get constructor position)
            (probe arity (.get constructor position))
              (bundle arity constructor (fun other => Source.embed (arguments other)))) ∧
          result = RawArrow.value (Source.classEmbedding (classOf (arguments position)))) ∨
        (label.fill supplied = classOf (cut arity (.build constructor)
          (probe arity (.build constructor))
            (bundle arity constructor (fun other => Source.embed (arguments other)))) ∧
          result = RawArrow.value (Source.classEmbedding (classOf (Source.sourceNode constructor arguments)))) := by
  obtain ⟨rule, ⟨occurrence, rfl⟩, reaction, square, _minimal, output⟩ := step
  have leftCount : arrowObserverCount (RawArrow.value supplied ≫ RawArrow.context label) = 3 := completeSupport
  have measure : arrowObserverCount occurrence.rule.redex + arrowObserverCount reaction = 3 :=
    (arrowCount_comp occurrence.rule.redex reaction).symm.trans
      ((congrArg arrowObserverCount square).symm.trans leftCount)
  cases occurrence with
  | ask suppliedOrigin found arguments =>
    rw [ask_redex_support] at measure
    cases reaction with
    | context context =>
      have bounded := classContextObserverCount_bundle_to_base found context
      change 2 ≤ arrowObserverCount (RawArrow.context context) at bounded
      omega
  | get suppliedOrigin found arguments position =>
    rw [get_redex_support] at measure
    have reactionPure : arrowObserverCount reaction = 0 := by omega
    have argumentSum : (∑ other, observerCount (arguments other)) = 0 := by omega
    cases reaction with
    | context context =>
      have inputRead : label.fill supplied = context.fill
          (classOf (cut arity (.get found position) (probe arity (.get found position))
            (bundle arity found arguments))) := RawArrow.value.inj square
      have contextIdentity := pure_context_unit_erasure_identity context reactionPure
        (classOf (cut arity (.get found position) (probe arity (.get found position))
          (bundle arity found arguments)))
        (erasure_probeCut (.get found position) (bundle arity found arguments))
        ((congrArg Source.classRetraction inputRead).symm.trans erasedInput)
      have reactionRead : RawArrow.context context = (𝟙 (.interface .base : ContextCategory arity)) :=
        congrArg RawArrow.context contextIdentity
      rw [reactionRead] at square output
      have square := square.trans
        (Category.comp_id (Occurrence.get suppliedOrigin found arguments position : Occurrence arity Origins).rule.redex)
      have output := output.trans
        (Category.comp_id (Occurrence.get suppliedOrigin found arguments position : Occurrence arity Origins).rule.reactum)
      have argumentsPure : ∀ other, observerCount (arguments other) = 0 := by
        intro other
        have bounded := Finset.single_le_sum (fun index _ => Nat.zero_le (observerCount (arguments index)))
          (Finset.mem_univ other)
        omega
      let before : Fin (sourceArity arity found) → Source.Value arity :=
        fun other => Source.erase (arguments other)
      have argumentsRead : (fun other => Source.embed (before other)) = arguments :=
        funext (fun other => observerCount_zero_readback (arguments other) (argumentsPure other))
      refine ⟨suppliedOrigin, found, before, Or.inl ⟨position, ?_, ?_⟩⟩
      · exact (RawArrow.value.inj square).trans
          (congrArg (fun arguments => classOf (cut arity (.get found position)
            (probe arity (.get found position)) (bundle arity found arguments))) argumentsRead).symm
      · exact output.trans
          (congrArg (fun (arguments : Fin (sourceArity arity found) → Value arity .base) =>
            (RawArrow.value (classOf (arguments position)) :
              (.origin : ContextCategory arity) ⟶ .interface .base)) argumentsRead).symm
  | build suppliedOrigin found arguments =>
    rw [build_redex_support] at measure
    have reactionPure : arrowObserverCount reaction = 0 := by omega
    have argumentSum : (∑ other, observerCount (arguments other)) = 0 := by omega
    cases reaction with
    | context context =>
      have inputRead : label.fill supplied = context.fill
          (classOf (cut arity (.build found) (probe arity (.build found))
            (bundle arity found arguments))) := RawArrow.value.inj square
      have contextIdentity := pure_context_unit_erasure_identity context reactionPure
        (classOf (cut arity (.build found) (probe arity (.build found)) (bundle arity found arguments)))
        (erasure_probeCut (.build found) (bundle arity found arguments))
        ((congrArg Source.classRetraction inputRead).symm.trans erasedInput)
      have reactionRead : RawArrow.context context = (𝟙 (.interface .base : ContextCategory arity)) :=
        congrArg RawArrow.context contextIdentity
      rw [reactionRead] at square output
      have square := square.trans
        (Category.comp_id (Occurrence.build suppliedOrigin found arguments : Occurrence arity Origins).rule.redex)
      have output := output.trans
        (Category.comp_id (Occurrence.build suppliedOrigin found arguments : Occurrence arity Origins).rule.reactum)
      have argumentsPure : ∀ other, observerCount (arguments other) = 0 := by
        intro other
        have bounded := Finset.single_le_sum (fun index _ => Nat.zero_le (observerCount (arguments index)))
          (Finset.mem_univ other)
        omega
      let before : Fin (sourceArity arity found) → Source.Value arity :=
        fun other => Source.erase (arguments other)
      have argumentsRead : (fun other => Source.embed (before other)) = arguments :=
        funext (fun other => observerCount_zero_readback (arguments other) (argumentsPure other))
      refine ⟨suppliedOrigin, found, before, Or.inr ⟨?_, ?_⟩⟩
      · exact (RawArrow.value.inj square).trans
          (congrArg (fun arguments => classOf (cut arity (.build found)
            (probe arity (.build found)) (bundle arity found arguments))) argumentsRead).symm
      · exact output.trans
          ((congrArg (fun arguments => RawArrow.value (classOf (sourceNode arity found arguments))) argumentsRead).symm.trans
            (congrArg (fun value => RawArrow.value (classOf value)) (Source.sourceNode_embed found before)).symm)

end Mettapedia.OSLF.Framework.SortedCommutativeInstruments
