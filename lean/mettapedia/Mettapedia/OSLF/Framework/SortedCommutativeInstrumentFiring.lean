import Mettapedia.OSLF.Framework.SortedCommutativeInstrumentProfile
import Mettapedia.OSLF.Syntax.SortedCommutativeContextMonomorphisms

/-!
# Actual sorted probe-labelled firing and retained receipts

The complete probe-filling equation and earned arrow monicity establish the
actual IPO universal property. Every supplied ask/get/build occurrence gives
a literal probe-labelled transition, with its entire raw argument tuple,
selected position and independently supplied origin retained beside the step.
No inhabited-origin assumption or deterministic quotient root view is used.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.Framework.SortedCommutativeInstruments

open _root_.CategoryTheory
open Mettapedia.OSLF.SortedCommutative
open Mettapedia.GSLT.RedexRelativeCongruence

universe u w

variable {Symbols : Type u} (arity : Symbols → Nat) {Origins : Type w}

def directRule (instrument : Probe arity)
    (body : Value arity (InstrumentCutContexts.receiver (sourceArity arity) instrument))
    (output : Value arity (InstrumentCutContexts.result (sourceArity arity) instrument)) :
    ReactionRule (.origin : ContextCategory arity) where
  codomain := .interface (InstrumentCutContexts.result (sourceArity arity) instrument)
  redex := RawArrow.value (classOf (cut arity instrument (probe arity instrument) body))
  reactum := RawArrow.value (classOf output)

theorem direct_step (instrument : Probe arity)
    (body : Value arity (InstrumentCutContexts.receiver (sourceArity arity) instrument))
    (output : Value arity (InstrumentCutContexts.result (sourceArity arity) instrument))
    (admitted : rules arity Origins (directRule arity instrument body output)) :
    ActIPO (rules arity Origins)
      (RawArrow.context (contextClassOf (probeContext arity instrument)) :
        (.interface (InstrumentCutContexts.receiver (sourceArity arity) instrument) : ContextCategory arity) ⟶
          .interface (InstrumentCutContexts.result (sourceArity arity) instrument))
      (RawArrow.value (classOf body)) (RawArrow.value (classOf output)) := by
  let chosen := directRule arity instrument body output
  have square : (RawArrow.value (classOf body) : (.origin : ContextCategory arity) ⟶
      .interface (InstrumentCutContexts.receiver (sourceArity arity) instrument)) ≫
        RawArrow.context (contextClassOf (probeContext arity instrument)) = chosen.redex :=
    congrArg RawArrow.value (congrArg classOf (probeContext_fill arity instrument body))
  refine ⟨chosen, admitted, 𝟙 _, square.trans (Category.comp_id chosen.redex).symm, ?_, ?_⟩
  · exact raw_right_identity_isIPO _ square
  · exact (Category.comp_id chosen.reactum).symm

variable {arity}

def Occurrence.instrument : Occurrence arity Origins → Probe arity
  | .ask _ constructor _ => .ask constructor
  | .get _ constructor _ position => .get constructor position
  | .build _ constructor _ => .build constructor

def Occurrence.body (supplied : Occurrence arity Origins) :
    Value arity (InstrumentCutContexts.receiver (sourceArity arity) supplied.instrument) :=
  match supplied with
  | .ask _ constructor arguments => sourceNode arity constructor arguments
  | .get _ constructor arguments _ => bundle arity constructor arguments
  | .build _ constructor arguments => bundle arity constructor arguments

def Occurrence.output (supplied : Occurrence arity Origins) :
    Value arity (InstrumentCutContexts.result (sourceArity arity) supplied.instrument) :=
  match supplied with
  | .ask _ constructor arguments => bundle arity constructor arguments
  | .get _ _ arguments position => arguments position
  | .build _ constructor arguments => sourceNode arity constructor arguments

def Occurrence.label (supplied : Occurrence arity Origins) :
    (.interface (InstrumentCutContexts.receiver (sourceArity arity) supplied.instrument) : ContextCategory arity) ⟶
      .interface (InstrumentCutContexts.result (sourceArity arity) supplied.instrument) :=
  RawArrow.context (contextClassOf (probeContext arity supplied.instrument))

def Occurrence.agent (supplied : Occurrence arity Origins) :
    (.origin : ContextCategory arity) ⟶
      .interface (InstrumentCutContexts.receiver (sourceArity arity) supplied.instrument) :=
  RawArrow.value (classOf supplied.body)

def Occurrence.target (supplied : Occurrence arity Origins) :
    (.origin : ContextCategory arity) ⟶
      .interface (InstrumentCutContexts.result (sourceArity arity) supplied.instrument) :=
  RawArrow.value (classOf supplied.output)

theorem Occurrence.direct_step (supplied : Occurrence arity Origins) :
    ActIPO (rules arity Origins) supplied.label supplied.agent supplied.target := by
  cases supplied with
  | ask origin constructor arguments =>
    exact SortedCommutativeInstruments.direct_step arity (.ask constructor) (sourceNode arity constructor arguments) (bundle arity constructor arguments)
      ⟨.ask origin constructor arguments, rfl⟩
  | get origin constructor arguments position =>
    exact SortedCommutativeInstruments.direct_step arity (.get constructor position) (bundle arity constructor arguments) (arguments position)
      ⟨.get origin constructor arguments position, rfl⟩
  | build origin constructor arguments =>
    exact SortedCommutativeInstruments.direct_step arity (.build constructor) (bundle arity constructor arguments) (sourceNode arity constructor arguments)
      ⟨.build origin constructor arguments, rfl⟩

structure FiringReceipt (arity : Symbols → Nat) (Origins : Type w) where
  occurrence : Occurrence arity Origins
  step : ActIPO (rules arity Origins) occurrence.label occurrence.agent occurrence.target

def directReceipt (supplied : Occurrence arity Origins) : FiringReceipt arity Origins :=
  ⟨supplied, supplied.direct_step⟩

theorem directReceipt_injective : Function.Injective (directReceipt (arity := arity) (Origins := Origins)) :=
  fun _ _ same => congrArg FiringReceipt.occurrence same

end Mettapedia.OSLF.Framework.SortedCommutativeInstruments
