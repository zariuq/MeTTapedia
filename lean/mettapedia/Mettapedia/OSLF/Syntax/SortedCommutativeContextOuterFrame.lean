import Mettapedia.OSLF.Syntax.SortedCommutativeContextCategory

/-!
# Complete outer frames at nonparallel context targets

A one-hole context whose target has no parallel structure, and differs from
its source, has an actual outer free-constructor frame. The constructor,
selected position, all sibling terms and inner context are retained. The
endpoint comparison merely transports the independently declared output sort.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.SortedCommutative

universe u v

variable {signature : Mettapedia.OSLF.SortedConstructors.Signature.{u,v}}
variable {Parallel : signature.Srt → Prop}

theorem RawContext.outer_frame_of_nonparallel {source target : signature.Srt}
    (context : RawContext signature Parallel source target)
    (different : source ≠ target) (notParallel : ¬Parallel target) :
    ∃ constructor : signature.Constructor,
      ∃ position : Fin (signature.arity constructor),
      ∃ siblings : (other : Fin (signature.arity constructor)) → other ≠ position →
          Term signature Parallel (signature.input constructor other),
      ∃ inner : RawContext signature Parallel source (signature.input constructor position),
      ∃ _outputRead : signature.output constructor = target,
        HEq (RawContext.frame constructor position siblings inner) context := by
  cases context with
  | hole => exact (different rfl).elim
  | frame constructor position siblings inner =>
    exact ⟨constructor, position, siblings, inner, rfl, HEq.rfl⟩
  | left parallel => exact (notParallel parallel).elim
  | right parallel => exact (notParallel parallel).elim

theorem RawContext.fill_class_heq {source before after : signature.Srt}
    (first : RawContext signature Parallel source before)
    (second : RawContext signature Parallel source after)
    (outputRead : before = after) (same : HEq first second)
    (supplied : Term signature Parallel source) :
    HEq (classOf (first.fill supplied)) (classOf (second.fill supplied)) := by
  subst after
  exact heq_of_eq (congrArg (fun context => classOf (context.fill supplied)) (eq_of_heq same))

end Mettapedia.OSLF.SortedCommutative
