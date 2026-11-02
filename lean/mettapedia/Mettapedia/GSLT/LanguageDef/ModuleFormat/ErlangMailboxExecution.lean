import Mettapedia.GSLT.LanguageDef.ModuleFormat.ErlangMailboxSteps

/-! The authored mailbox rules realize the independent queue operations.
Finite completion and completed-answer reflection are proved for arbitrary
queue lengths and payloads. Rotation and prefix restoration are internal
paths, not additional source queue operations. -/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.ErlangMailbox.Execution

open Mettapedia.OSLF.MeTTaIL Syntax ContextualStep
open Mettapedia.Languages.Erlang

abbrev Path (base : BasePremiseEvaluator) := Relation.ReflTransGen (ContextualStep.Step base language)

def Normal (base : BasePremiseEvaluator) (source : Pattern) : Prop :=
  ∀ target, ¬ ContextualStep.Step base language source target

/-- Both existence and no-invention, without assuming a source result or
restricting the completed target to the encoding image. -/
structure Settles (base : BasePremiseEvaluator) (source answer : Pattern) : Prop where
  reached : Path base source answer
  normal : Normal base answer
  exact : ∀ target, Path base source target → Normal base target → target = answer

private theorem settles_stop (base : BasePremiseEvaluator) (source : Pattern) (normal : Normal base source) :
    Settles base source source := by
  refine ⟨.refl, normal, ?_⟩
  intro target path _
  rcases path.cases_head with same | ⟨next, step, _⟩
  · exact same.symm
  · exact False.elim (normal next step)

private theorem settles_prepend {base : BasePremiseEvaluator} {source middle answer : Pattern}
    (unique : ∀ target, ContextualStep.Step base language source target ↔ target = middle)
    (rest : Settles base middle answer) : Settles base source answer := by
  have first := (unique middle).mpr rfl
  refine ⟨rest.reached.head first, rest.normal, ?_⟩
  intro target path normal
  rcases path.cases_head with same | ⟨next, step, remaining⟩
  · subst target
    exact False.elim (normal middle first)
  · have same := (unique next).mp step
    subst next
    exact rest.exact target remaining normal

private theorem answer_settles (base : BasePremiseEvaluator) (label : String) (arguments : List Pattern)
    (member : label ∈ ["ErPeekValue", "ErPeekEmpty", "ErAdvanced", "ErRemoved", "ErDelivered", "ErReady", "ErWaiting"]) :
    Settles base (node label arguments) (node label arguments) :=
  settles_stop base _ (answer_no_step base label arguments member)

variable {α : Type*}

def peekAnswer (encode : α → Pattern) (box : Mailbox α) : Pattern :=
  match box.peek with
  | some head => node "ErPeekValue" [encode head, mailbox encode box.normalize]
  | none => node "ErPeekEmpty" [mailbox encode box.normalize]

def waitAnswer (encode : α → Pattern) (box : Mailbox α) : Pattern :=
  node (if box.unread.isEmpty then "ErWaiting" else "ErReady") [mailbox encode box]

theorem peek_front (base : BasePremiseEvaluator) (encode : α → Pattern)
    (saved : List α) (head : α) (tail rear : List α) :
    Settles base (node "ErPeek" [mailbox encode ⟨saved, head :: tail, rear⟩])
      (peekAnswer encode ⟨saved, head :: tail, rear⟩) := by
  have done := settles_prepend
    (peek_value_iff base (values (saved.map encode)) (encode head) (values (tail.map encode))
      (values (rear.map encode)))
    (answer_settles base "ErPeekValue"
      [encode head, mailbox encode ⟨saved, head :: tail, rear⟩] (by simp))
  simpa only [mailbox, values, peekAnswer, Mailbox.peek, Mailbox.unread, List.cons_append,
    List.head?_cons, Mailbox.normalize, List.map_cons] using done

theorem peek_empty (base : BasePremiseEvaluator) (encode : α → Pattern) (saved : List α) :
    Settles base (node "ErPeek" [mailbox encode ⟨saved, [], []⟩])
      (peekAnswer encode ⟨saved, [], []⟩) := by
  have done := settles_prepend (peek_empty_iff base (values (saved.map encode)))
    (answer_settles base "ErPeekEmpty" [mailbox encode ⟨saved, [], []⟩] (by simp))
  simpa [mailbox, values, peekAnswer, Mailbox.peek, Mailbox.unread, Mailbox.normalize] using done

theorem rotate (base : BasePremiseEvaluator) (encode : α → Pattern) (saved front rear : List α) :
    Settles base
      (node "ErRotate" [values (saved.map encode), values (front.map encode), values (rear.map encode)])
      (peekAnswer encode ⟨saved, rear.reverse ++ front, []⟩) := by
  induction rear generalizing front with
  | nil =>
      have peek : Settles base (node "ErPeek" [mailbox encode ⟨saved, front, []⟩])
          (peekAnswer encode ⟨saved, front, []⟩) := by
        cases front with
        | nil => exact peek_empty base encode saved
        | cons head tail => exact peek_front base encode saved head tail []
      simpa [mailbox, values] using settles_prepend
        (rotate_done_iff base (values (saved.map encode)) (values (front.map encode))) peek
  | cons head tail ih =>
      have done := settles_prepend
        (rotate_more_iff base (values (saved.map encode)) (values (front.map encode))
          (encode head) (values (tail.map encode))) (ih (head :: front))
      simpa only [List.map_cons, values, List.reverse_cons, List.append_assoc, List.singleton_append] using done

theorem peek (base : BasePremiseEvaluator) (encode : α → Pattern) (box : Mailbox α) :
    Settles base (node "ErPeek" [mailbox encode box]) (peekAnswer encode box) := by
  rcases box with ⟨saved, front, rear⟩
  cases front with
  | cons head tail => exact peek_front base encode saved head tail rear
  | nil =>
      cases rear with
      | nil => exact peek_empty base encode saved
      | cons head tail =>
          have done := settles_prepend
            (peek_rotate_iff base (values (saved.map encode)) (encode head) (values (tail.map encode)))
            (rotate base encode saved [head] tail)
          have agrees : peekAnswer encode (Mailbox.mk saved (tail.reverse ++ [head]) []) =
              peekAnswer encode ⟨saved, [], head :: tail⟩ := by
            cases reversed : tail.reverse <;>
              simp [peekAnswer, Mailbox.peek, Mailbox.unread, Mailbox.normalize, reversed]
          simpa only [mailbox, List.map_nil, List.map_cons, values, agrees] using done

theorem restore (base : BasePremiseEvaluator) (encode : α → Pattern) (saved front rear : List α) :
    Settles base (node "ErRestore" [values (saved.map encode), values (front.map encode), values (rear.map encode)])
      (node "ErRemoved" [mailbox encode ⟨[], saved.reverse ++ front, rear⟩]) := by
  induction saved generalizing front with
  | nil =>
      simpa [mailbox, values] using settles_prepend
        (restore_done_iff base (values (front.map encode)) (values (rear.map encode)))
        (answer_settles base "ErRemoved" [mailbox encode ⟨[], front, rear⟩] (by simp))
  | cons head tail ih =>
      have done := settles_prepend
        (restore_more_iff base (encode head) (values (tail.map encode))
          (values (front.map encode)) (values (rear.map encode))) (ih (head :: front))
      simpa only [List.map_cons, values, List.reverse_cons, List.append_assoc, List.singleton_append] using done

theorem next (base : BasePremiseEvaluator) (encode : α → Pattern) {box result : Mailbox α}
    (authorized : box.next? = some result) :
    Settles base (node "ErNext" [mailbox encode box]) (node "ErAdvanced" [mailbox encode result]) := by
  rcases box with ⟨saved, front, rear⟩
  cases front with
  | nil => simp [Mailbox.next?] at authorized
  | cons head tail =>
      have same : result = ⟨head :: saved, tail, rear⟩ := by
        simpa only [Mailbox.next?, Option.some.injEq] using authorized.symm
      subst result
      simpa [mailbox, values] using settles_prepend
        (next_iff base (values (saved.map encode)) (encode head) (values (tail.map encode))
          (values (rear.map encode)))
        (answer_settles base "ErAdvanced" [mailbox encode ⟨head :: saved, tail, rear⟩] (by simp))

theorem remove (base : BasePremiseEvaluator) (encode : α → Pattern) {box result : Mailbox α}
    (authorized : box.remove? = some result) :
    Settles base (node "ErRemove" [mailbox encode box]) (node "ErRemoved" [mailbox encode result]) := by
  rcases box with ⟨saved, front, rear⟩
  cases front with
  | nil => simp [Mailbox.remove?] at authorized
  | cons head tail =>
      have same : result = ⟨[], saved.reverse ++ tail, rear⟩ := by
        simpa only [Mailbox.remove?, Option.some.injEq] using authorized.symm
      subst result
      simpa [mailbox, values] using settles_prepend
        (remove_iff base (values (saved.map encode)) (encode head) (values (tail.map encode))
          (values (rear.map encode))) (restore base encode saved tail rear)

theorem deliver (base : BasePremiseEvaluator) (encode : α → Pattern) (message : α) (box : Mailbox α) :
    Settles base (node "ErDeliver" [encode message, mailbox encode box])
      (node "ErDelivered" [mailbox encode (box.deliver message)]) := by
  rcases box with ⟨saved, front, rear⟩
  simpa [mailbox, values, Mailbox.deliver] using settles_prepend
    (deliver_iff base (encode message) (values (saved.map encode)) (values (front.map encode))
      (values (rear.map encode)))
    (answer_settles base "ErDelivered" [mailbox encode (Mailbox.deliver message ⟨saved, front, rear⟩)] (by simp))

theorem wait (base : BasePremiseEvaluator) (encode : α → Pattern) (box : Mailbox α) :
    Settles base (node "ErWait" [mailbox encode box]) (waitAnswer encode box) := by
  rcases box with ⟨saved, front, rear⟩
  cases front with
  | cons head tail =>
      simpa [waitAnswer, Mailbox.unread, mailbox, values] using settles_prepend
        (wait_front_iff base (values (saved.map encode)) (encode head) (values (tail.map encode))
          (values (rear.map encode)))
        (answer_settles base "ErReady" [mailbox encode ⟨saved, head :: tail, rear⟩] (by simp))
  | nil =>
      cases rear with
      | nil =>
          simpa [waitAnswer, Mailbox.unread, mailbox, values] using settles_prepend
            (wait_empty_iff base (values (saved.map encode)))
            (answer_settles base "ErWaiting" [mailbox encode ⟨saved, [], []⟩] (by simp))
      | cons head tail =>
          simpa [waitAnswer, Mailbox.unread, mailbox, values] using settles_prepend
            (wait_rear_iff base (values (saved.map encode)) (encode head) (values (tail.map encode)))
            (answer_settles base "ErReady" [mailbox encode ⟨saved, [], head :: tail⟩] (by simp))

theorem wake (base : BasePremiseEvaluator) (encode : α → Pattern) (message : α) (saved : List α) :
    Settles base (node "ErWake" [encode message, mailbox encode ⟨saved, [], []⟩])
      (node "ErReady" [mailbox encode (Mailbox.deliver message ⟨saved, [], []⟩)]) := by
  simpa [mailbox, values, Mailbox.deliver] using settles_prepend
    (wake_iff base (encode message) (values (saved.map encode)))
    (answer_settles base "ErReady" [mailbox encode (Mailbox.deliver message ⟨saved, [], []⟩)] (by simp))

end Mettapedia.GSLT.LanguageDef.ModuleFormat.ErlangMailbox.Execution
