import Mettapedia.OSLF.Framework.SortedCommutativeProbeSupport
import Mettapedia.OSLF.Syntax.SortedCommutativeConstructorReadout

/-!
# Full-family ask IPO inversion on complete source equation classes

An actual ask-labelled step is inspected against every independently supplied
administrative declaration. Complete support excludes get and build rules,
forces a pure argument tuple and a literal identity reaction context, and
recovers the supplied origin. Cancellation of the actual probe context
recovers source constructor matching; the full bundle target is retained.

Matching the original AC1 Cut remains an existential decomposition into an
ordered pair. The theorem does not select a root view or erase competing
decompositions. Origins are supplied by the actual step; none are assumed
inhabited when reconstructing a firing.
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

def Source.sourceNode (constructor : SourceSymbol Symbols)
    (arguments : Fin (sourceArity arity constructor) → Source.Value arity) : Source.Value arity :=
  match constructor with
  | .ordinary symbol => Term.node (signature := Source.signature arity) symbol arguments
  | .properCut => .cut rfl (arguments 0) (arguments 1)
  | .unit => .zero rfl

theorem Source.sourceNode_embed (constructor : SourceSymbol Symbols)
    (arguments : Fin (sourceArity arity constructor) → Source.Value arity) :
    Source.embed (Source.sourceNode constructor arguments) =
      SortedCommutativeInstruments.sourceNode arity constructor (fun position => Source.embed (arguments position)) := by
  cases constructor <;> rfl

def askLabel (constructor : SourceSymbol Symbols) :
    (.interface .base : ContextCategory arity) ⟶ .interface (.arguments constructor) :=
  RawArrow.context (contextClassOf (probeContext arity (.ask constructor)))

theorem askLabel_support (constructor : SourceSymbol Symbols) :
    arrowObserverCount (askLabel (arity := arity) constructor) = 2 :=
  contextObserverCount_probeContext (.ask constructor)

theorem ask_source_step_iff (constructor : SourceSymbol Symbols) (supplied : Source.ValueClass arity)
    (result : (.origin : ContextCategory arity) ⟶ .interface (.arguments constructor)) :
    ActIPO (rules arity Origins) (askLabel constructor) (RawArrow.value (Source.classEmbedding supplied)) result ↔
      ∃ _suppliedOrigin : Origins, ∃ arguments : Fin (sourceArity arity constructor) → Source.Value arity,
        supplied = classOf (Source.sourceNode constructor arguments) ∧
          result = RawArrow.value (classOf (bundle arity constructor (fun position => Source.embed (arguments position)))) := by
  constructor
  · intro step
    obtain ⟨rule, ⟨occurrence, rfl⟩, reaction, square, _minimal, output⟩ := step
    have agentPure : arrowObserverCount
        (RawArrow.value (Source.classEmbedding supplied) : (.origin : ContextCategory arity) ⟶ .interface .base) = 0 :=
      classObserverCount_embedding supplied
    have leftCount : arrowObserverCount (RawArrow.value (Source.classEmbedding supplied) ≫ askLabel constructor) = 2 := by
      rw [arrowCount_comp, agentPure, askLabel_support]
    have measure : arrowObserverCount occurrence.rule.redex + arrowObserverCount reaction = 2 :=
      (arrowCount_comp occurrence.rule.redex reaction).symm.trans
        ((congrArg arrowObserverCount square).symm.trans leftCount)
    cases occurrence with
    | ask suppliedOrigin found arguments =>
      rw [ask_redex_support] at measure
      have reactionPure : arrowObserverCount reaction = 0 := by omega
      have argumentSum : (∑ position, observerCount (arguments position)) = 0 := by omega
      cases reaction with
      | context suppliedContext =>
        change classContextObserverCount suppliedContext = 0 at reactionPure
        obtain ⟨same, contextRead⟩ := classContextObserverCount_zero_nonbase_identity
          (show (.arguments found : Srt arity) ≠ .base from by intro impossible; cases impossible)
          suppliedContext reactionPure
        have foundSame : constructor = found := InstrumentCutContexts.Srt.arguments.inj same
        subst found
        have reactionRead : RawArrow.context suppliedContext =
            (𝟙 (.interface (.arguments constructor) : ContextCategory arity)) :=
          congrArg RawArrow.context (eq_of_heq contextRead)
        rw [reactionRead] at square output
        have square := square.trans
          (Category.comp_id (Occurrence.ask suppliedOrigin constructor arguments : Occurrence arity Origins).rule.redex)
        have output := output.trans
          (Category.comp_id (Occurrence.ask suppliedOrigin constructor arguments : Occurrence arity Origins).rule.reactum)
        have argumentsPure : ∀ position, observerCount (arguments position) = 0 := by
          intro position
          have bounded := Finset.single_le_sum (fun other _ => Nat.zero_le (observerCount (arguments other)))
            (Finset.mem_univ position)
          omega
        let before : Fin (sourceArity arity constructor) → Source.Value arity :=
          fun position => Source.erase (arguments position)
        have argumentsRead : (fun position => Source.embed (before position)) = arguments :=
          funext (fun position => observerCount_zero_readback (arguments position) (argumentsPure position))
        have bodySquare :
            (RawArrow.value (classOf (sourceNode arity constructor arguments)) :
              (.origin : ContextCategory arity) ⟶ .interface .base) ≫ askLabel constructor =
              (Occurrence.ask suppliedOrigin constructor arguments : Occurrence arity Origins).rule.redex :=
          congrArg RawArrow.value (congrArg classOf (probeContext_fill arity (.ask constructor)
            (sourceNode arity constructor arguments)))
        have inputRead : Source.classEmbedding supplied = classOf (sourceNode arity constructor arguments) :=
          RawArrow.value.inj ((cancel_mono (askLabel constructor)).mp (square.trans bodySquare.symm))
        have wholeBodyRead : Source.classEmbedding (classOf (Source.sourceNode constructor before)) =
            classOf (sourceNode arity constructor arguments) :=
          (congrArg classOf (Source.sourceNode_embed constructor before)).trans
            (congrArg (fun arguments => classOf (sourceNode arity constructor arguments)) argumentsRead)
        refine ⟨suppliedOrigin, before, Source.classEmbedding_injective (inputRead.trans wholeBodyRead.symm), ?_⟩
        exact output.trans (congrArg (fun arguments => RawArrow.value (classOf (bundle arity constructor arguments))) argumentsRead).symm
    | get suppliedOrigin found arguments position =>
      rw [get_redex_support] at measure
      omega
    | build suppliedOrigin found arguments =>
      rw [build_redex_support] at measure
      omega
  · rintro ⟨suppliedOrigin, arguments, rfl, resultRead⟩
    have bodyRead : Source.classEmbedding (classOf (Source.sourceNode constructor arguments)) =
        classOf (sourceNode arity constructor (fun position => Source.embed (arguments position))) :=
      congrArg classOf (Source.sourceNode_embed constructor arguments)
    rw [bodyRead, resultRead]
    exact (Occurrence.ask suppliedOrigin constructor (fun position => Source.embed (arguments position))).direct_step

theorem ordinary_ask_step_iff (constructor : Symbols)
    (arguments : Fin (arity constructor) → Source.Value arity)
    (result : (.origin : ContextCategory arity) ⟶ .interface (.arguments (.ordinary constructor))) :
    ActIPO (rules arity Origins) (askLabel (.ordinary constructor))
      (RawArrow.value (Source.classEmbedding (classOf (Source.sourceNode (.ordinary constructor) arguments)))) result ↔
        Nonempty Origins ∧ result = RawArrow.value
          (classOf (bundle arity (.ordinary constructor) (fun position => Source.embed (arguments position)))) := by
  constructor
  · intro step
    obtain ⟨suppliedOrigin, matchedArguments, sourceRead, targetRead⟩ :=
      (ask_source_step_iff (.ordinary constructor) _ result).mp step
    have coordinates : ∀ position, classOf (arguments position) = classOf (matchedArguments position) :=
      (node_class_eq_iff (signature := Source.signature arity) (Parallel := Source.Parallel arity)
        constructor arguments matchedArguments).mp sourceRead
    have bundleRead :
        classOf (bundle arity (.ordinary constructor) (fun position => Source.embed (arguments position))) =
          classOf (bundle arity (.ordinary constructor) (fun position => Source.embed (matchedArguments position))) :=
      (node_class_eq_iff (signature := signature arity) (Parallel := Parallel arity)
        (.arguments (.ordinary constructor)) (fun position => Source.embed (arguments position))
          (fun position => Source.embed (matchedArguments position))).mpr
        (fun position => congrArg Source.classEmbedding (coordinates position))
    exact ⟨⟨suppliedOrigin⟩, targetRead.trans (congrArg RawArrow.value bundleRead).symm⟩
  · rintro ⟨⟨suppliedOrigin⟩, targetRead⟩
    exact (ask_source_step_iff (.ordinary constructor) _ result).mpr
      ⟨suppliedOrigin, arguments, rfl, targetRead⟩

end Mettapedia.OSLF.Framework.SortedCommutativeInstruments
