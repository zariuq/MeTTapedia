import Mettapedia.OSLF.Framework.InstrumentSourceRelativePushout

/-!
# Recovering a source context from its complete constructor readout

Every frame of a context producing an embedded source tree is reconstructed
from that actual tree, including its selected position and all siblings.
This permits reaction-context reflection without assuming faithful ground
action: distinct positions may still produce the same filled ground value.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.Framework.InstrumentCutContexts

open _root_.CategoryTheory
open Mettapedia.OSLF.SortedConstructors
open Mettapedia.CategoryTheory.GroundPath

universe u

variable {Symbols : Type u} (arity : Symbols → Nat)

local instance instrumentSourceFillingQuiver : Quiver (Srt Symbols arity) := frameQuiver (signature arity)

theorem source_frame_fill_lift {source : Srt Symbols arity}
    (frame : Frame (signature arity) source .base) (supplied : Value arity source)
    (head : Symbols) (arguments : Fin (arity head) → InstrumentObservations.Tree Symbols arity)
    (readout : frame.fill supplied = embedSource arity (.node head arguments)) :
    ∃ position : Fin (arity head), source = .base ∧
      HEq frame (sourceFrameImage arity ⟨head, position, fun other _ => arguments other⟩) ∧
      HEq supplied (embedSource arity (arguments position)) := by
  classical
  have heads : frame.constructor = Constructor.original head :=
    (Frame.fill_head frame supplied).symm.trans (Term.head_eq _ _ readout)
  obtain ⟨position, siblings, sourceEq, _, frameEq⟩ := Frame.deconstruct frame (Constructor.original head) heads
  cases sourceEq
  cases eq_of_heq frameEq
  have allArguments := Term.node.inj readout
  have selected : supplied = embedSource arity (arguments position) := by
    simpa [embedSource] using congrFun allArguments position
  have siblingRead : siblings = fun other (_ : other ≠ position) => embedSource arity (arguments other) := by
    funext other absent
    simpa only [dif_neg absent, embedSource] using congrFun allArguments other
  cases siblingRead
  exact ⟨position, rfl, HEq.rfl, heq_of_eq selected⟩

theorem source_context_fill_lift (suppliedContext : Context (signature arity) .base .base)
    (first second : InstrumentObservations.Tree Symbols arity)
    (readout : (action (signature arity)).path suppliedContext (embedSource arity first) = embedSource arity second) :
    ∃ original : SourceContext arity, sourceContextImage arity original = suppliedContext ∧
      SourceContext.fill arity original first = second := by
  generalize counted : suppliedContext.length = count
  induction count using Nat.strong_induction_on generalizing suppliedContext first second with
  | h count inductionHypothesis =>
    cases suppliedContext with
    | nil => exact ⟨[], rfl, embedSource_injective arity readout⟩
    | @cons middle _ previous frame =>
      cases second with
      | node head arguments =>
        obtain ⟨position, middleEq, frameEq, inputRead⟩ := source_frame_fill_lift arity frame
          ((action (signature arity)).path previous (embedSource arity first)) head arguments readout
        cases middleEq
        have smaller : previous.length < count := by
          change previous.length + 1 = count at counted
          omega
        obtain ⟨original, contextRead, valueRead⟩ := inductionHypothesis previous.length smaller
          previous first (arguments position) (eq_of_heq inputRead) rfl
        let originalFrame : SourceFrame arity := ⟨head, position, fun other _ => arguments other⟩
        refine ⟨originalFrame :: original, ?_, ?_⟩
        · change (sourceContextImage arity original).cons (sourceFrameImage arity originalFrame) = previous.cons frame
          rw [contextRead, eq_of_heq frameEq]
        · change originalFrame.fill arity (SourceContext.fill arity original first) =
            InstrumentObservations.Tree.node head arguments
          rw [valueRead]
          apply congrArg (InstrumentObservations.Tree.node head)
          funext other
          split_ifs with same
          · exact congrArg arguments same.symm
          · rfl

end Mettapedia.OSLF.Framework.InstrumentCutContexts
