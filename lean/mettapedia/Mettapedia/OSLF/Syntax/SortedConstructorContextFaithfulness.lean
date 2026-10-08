import Mettapedia.OSLF.Syntax.SortedConstructorContexts

/-!
# Complete frame and one-hole syntax readouts

These readouts retain actual constructor names and positions. They distinguish
two paths even when inserting a particular ground value makes their resulting
closed constructor terms equal.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.SortedConstructors

universe u v

variable {signature : Signature.{u,v}}

namespace Term

def head : {sort : signature.Srt} → Term signature sort → signature.Constructor
  | _, .node constructor _ => constructor

theorem head_eq {sort : signature.Srt} (first second : Term signature sort)
    (same : first = second) : head first = head second := congrArg head same

end Term

namespace Frame

def constructor : {source target : signature.Srt} → Frame signature source target → signature.Constructor
  | _, _, .slot constructor _ _ => constructor

def position {source target : signature.Srt} (frame : Frame signature source target) :
    Fin (signature.arity frame.constructor) := by
  cases frame with
  | slot _ position _ => exact position

theorem output_eq {source target : signature.Srt} (frame : Frame signature source target) :
    signature.output frame.constructor = target := by cases frame; rfl

theorem input_eq {source target : signature.Srt} (frame : Frame signature source target) :
    signature.input frame.constructor frame.position = source := by cases frame; rfl

theorem fill_head {source target : signature.Srt} (frame : Frame signature source target)
    (supplied : Term signature source) : (frame.fill supplied).head = frame.constructor := by
  cases frame
  rfl

theorem deconstruct {source target : signature.Srt} (frame : Frame signature source target)
    (head : signature.Constructor) (same : frame.constructor = head) :
    ∃ position : Fin (signature.arity head),
      ∃ siblings : (other : Fin (signature.arity head)) → other ≠ position →
        Term signature (signature.input head other),
      source = signature.input head position ∧ target = signature.output head ∧
        HEq frame (Frame.slot head position siblings) := by
  cases frame with
  | slot constructor position siblings =>
    change constructor = head at same
    subst head
    exact ⟨position, siblings, rfl, rfl, HEq.rfl⟩

end Frame

namespace ContextSyntax

variable {holeSort : signature.Srt}

def head : {sort : signature.Srt} → ContextSyntax signature holeSort sort → Option signature.Constructor
  | _, .hole => none
  | _, .closed _ => none
  | _, .node constructor _ => some constructor

theorem wrap_head {source target : signature.Srt} (frame : Frame signature source target)
    (inner : ContextSyntax signature holeSort source) : head (wrap frame inner) = some frame.constructor := by
  cases frame
  rfl

theorem wrap_step_eq {firstSource secondSource target : signature.Srt}
    (firstFrame : Frame signature firstSource target)
    (secondFrame : Frame signature secondSource target)
    (first : ContextSyntax signature holeSort firstSource)
    (second : ContextSyntax signature holeSort secondSource)
    (firstCount : first.holeCount = 1)
    (same : wrap firstFrame first = wrap secondFrame second) :
    firstSource = secondSource ∧ HEq firstFrame secondFrame ∧ HEq first second := by
  classical
  have constructors := congrArg head same
  rw [wrap_head, wrap_head] at constructors
  have constructorsSame := Option.some.inj constructors
  cases firstFrame with
  | slot firstConstructor firstPosition firstSiblings =>
    obtain ⟨secondPosition, secondSiblings, sourceSame, _, secondFrameSame⟩ :=
      Frame.deconstruct secondFrame firstConstructor constructorsSame.symm
    cases sourceSame
    cases eq_of_heq secondFrameSame
    have arguments := ContextSyntax.node.inj same
    have positions : firstPosition = secondPosition := by
      by_contra different
      have counted := congrArg holeCount (congrFun arguments firstPosition)
      simp [different, holeCount, firstCount] at counted
    subst secondPosition
    have inner : first = second := by
      simpa using congrFun arguments firstPosition
    have siblings : firstSiblings = secondSiblings := by
      funext position absent
      have readout := congrFun arguments position
      simp only [dif_neg absent] at readout
      exact closed.inj readout
    subst secondSiblings
    exact ⟨rfl, HEq.rfl, heq_of_eq inner⟩

end ContextSyntax

theorem readContext_injective {source target : signature.Srt}
    (first second : Context signature source target)
    (same : readContext signature first = readContext signature second) : first = second := by
  induction first with
  | nil =>
    cases second with
    | nil => rfl
    | cons previous frame =>
      cases frame
      cases same
  | @cons middle target previous frame inductionHypothesis =>
    cases second with
    | nil =>
      cases frame
      cases same
    | cons otherPrevious otherFrame =>
      obtain ⟨middleSame, framesSame, innerSame⟩ := ContextSyntax.wrap_step_eq frame otherFrame
        (readContext signature previous) (readContext signature otherPrevious)
        (readContext_holeCount signature previous) same
      subst middleSame
      have contextsSame := inductionHypothesis otherPrevious (eq_of_heq innerSame)
      cases eq_of_heq framesSame
      exact congrArg (fun context => context.cons frame) contextsSame

end Mettapedia.OSLF.SortedConstructors
