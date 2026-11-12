import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.EventCategory
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Transport

/-!
# Exact continuation transport along equal native states

Equality casts preserve the entire firing word. Associativity of native run
composition therefore holds with its explicit endpoint cast. This transport
is separate from moving a run along a possibly nontrivial state isomorphism.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface

universe uO uT uH uOcc uS uF uI

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {X : Frames Tm Hom} {O : Type uOcc} [DecidableEq O]
  {State : Type uS} {Firing : State → Type uF} {P : Step X O State Firing}

namespace Step.Run

def castStart {s t : State} (same : s = t) (run : P.Run s) : P.Run t := same ▸ run

@[simp] theorem word_castStart {s t : State} (same : s = t) (run : P.Run s) :
    (castStart same run).word = run.word := by cases same; rfl

@[simp] theorem last_castStart {s t : State} (same : s = t) (run : P.Run s) :
    (castStart same run).last = run.last := by cases same; rfl

@[simp] theorem append_nil {s : State} (run : P.Run s) : run.append (.nil run.last) = run := by
  apply eq_of_word_eq P
  simp only [word_append, word, List.append_nil]

theorem append_castStart {s : State} (first : P.Run s) (second : P.Run first.last)
    (third : P.Run second.last) :
    (first.append second).append (castStart (first.last_append second).symm third) =
      first.append (second.append third) := by
  apply eq_of_word_eq P
  simp only [word_append, word_castStart, List.append_assoc]

end Step.Run

namespace Transport.Similar

variable {T : Transport.{uO,uT,uH,uOcc,uS,uF,uI} P}

theorem castStart {s t : State} (same : s = t) (run : P.Run s) :
    T.Similar run (Step.Run.castStart same run) := by
  cases same
  exact Similar.refl run

end Transport.Similar

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
