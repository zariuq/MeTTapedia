import Mathlib.Data.List.Basic

/-!
# Answer producers handed to equation search

Equation search reads a call's equation occurrences when the call is made, a
logical update view: a program change reaches later calls, not calls in
progress.  An answer producer enumerates the same occurrences under one fixed
program.  Its frontier is a stack of frames, each a relation, an argument and
the ordinal of the next untried occurrence; a call made by the last occurrence
of its caller replaces the caller.

`handoff` turns a frontier into the equation choices of its unfinished calls.
Under the producer's program each producer step is either a silent retirement
of a finished call, which leaves the handoff unchanged, or exactly the step
equation search takes from the handoff (`producerStep_simulates`).  The answers
a producer yields from a frontier are therefore exactly the answers equation
search yields from its handoff, in the same order, none lost and none repeated
(`producerRun_sound`, `producerRun_complete`).

A consumer that compares the program with the producer's before each further
answer may switch to equation search at any answer boundary: segments run
while the program is unchanged are segments of equation search, and after a
change equation search continues from the handoff, whose choices hold the
occurrences their calls read (`validated_producer_exact`).  Without the
comparison, a later call would miss equations added in between
(`unvalidated_producer_misses_new_equation`).
-/

namespace Mettapedia.Languages.MeTTa.AnswerProducerHandoff

universe u v

variable {Head : Type u} {Value : Type v}

/-- What a matching equation occurrence yields: an answer, or a last call. -/
inductive Outcome (Head : Type u) (Value : Type v) where
  | answer (value : Value)
  | call (head : Head) (argument : Value)

/-- An equation occurrence: its outcome on the arguments it matches. -/
abbrev Equation (Head : Type u) (Value : Type v) :=
  Value → Option (Outcome Head Value)

/-- The equation occurrences of each relation under one program revision, in
occurrence order. -/
abbrev Program (Head : Type u) (Value : Type v) :=
  Head → List (Equation Head Value)

/-! ## Equation search -/

/-- An equation choice: a call's argument and the occurrences it has not yet
tried, read from the program when the call was made. -/
structure Choice (Head : Type u) (Value : Type v) where
  argument : Value
  pending : List (Equation Head Value)

/-- Equation search keeps a choice only while it has alternatives. -/
def push (choice : Choice Head Value) (stack : List (Choice Head Value)) :
    List (Choice Head Value) :=
  if choice.pending.isEmpty then stack else choice :: stack

/-- One step of equation search: try the innermost choice's next occurrence.
A call reads its relation from `program`, the program when it is made. -/
def searchStep (program : Program Head Value) :
    List (Choice Head Value) → Option (Option Value × List (Choice Head Value))
  | [] => none
  | ⟨_, []⟩ :: rest => some (none, rest)
  | ⟨argument, equation :: others⟩ :: rest =>
      match equation argument with
      | none => some (none, push ⟨argument, others⟩ rest)
      | some (.answer value) => some (some value, push ⟨argument, others⟩ rest)
      | some (.call head next) =>
          some (none, push ⟨next, program head⟩ (push ⟨argument, others⟩ rest))

/-- Equation search from `start` yields `answers`, in order, and reaches
`finish`. -/
inductive SearchRun (program : Program Head Value) :
    List (Choice Head Value) → List Value → List (Choice Head Value) → Prop
  | stop (stack : List (Choice Head Value)) : SearchRun program stack [] stack
  | step {stack next finish : List (Choice Head Value)}
      {emitted : Option Value} {answers : List Value} :
      searchStep program stack = some (emitted, next) →
      SearchRun program next answers finish →
      SearchRun program stack (emitted.toList ++ answers) finish

/-! ## The answer producer -/

/-- A producer call: its relation, its argument, and the ordinal of its next
untried equation occurrence. -/
structure Frame (Head : Type u) (Value : Type v) where
  head : Head
  argument : Value
  next : Nat

/-- One producer step under the program it was compiled from.  A finished
call is retired; a call made by its caller's last occurrence replaces the
caller. -/
def producerStep (program : Program Head Value) :
    List (Frame Head Value) → Option (Option Value × List (Frame Head Value))
  | [] => none
  | frame :: rest =>
      match (program frame.head)[frame.next]? with
      | none => some (none, rest)
      | some equation =>
          match equation frame.argument with
          | none => some (none, { frame with next := frame.next + 1 } :: rest)
          | some (.answer value) =>
              some (some value, { frame with next := frame.next + 1 } :: rest)
          | some (.call head argument) =>
              if frame.next + 1 < (program frame.head).length then
                some (none, ⟨head, argument, 0⟩ ::
                  { frame with next := frame.next + 1 } :: rest)
              else
                some (none, ⟨head, argument, 0⟩ :: rest)

/-- The producer yields `answers` from `start` and reaches `finish`. -/
inductive ProducerRun (program : Program Head Value) :
    List (Frame Head Value) → List Value → List (Frame Head Value) → Prop
  | stop (frames : List (Frame Head Value)) : ProducerRun program frames [] frames
  | step {frames next finish : List (Frame Head Value)}
      {emitted : Option Value} {answers : List Value} :
      producerStep program frames = some (emitted, next) →
      ProducerRun program next answers finish →
      ProducerRun program frames (emitted.toList ++ answers) finish

/-- The equation choice a producer call stands for: its relation's
occurrences from its next ordinal on. -/
def Frame.choice (program : Program Head Value) (frame : Frame Head Value) :
    Choice Head Value :=
  ⟨frame.argument, (program frame.head).drop frame.next⟩

/-- The handoff of a frontier: the equation choices of its unfinished calls,
innermost first. -/
def handoff (program : Program Head Value) :
    List (Frame Head Value) → List (Choice Head Value)
  | [] => []
  | frame :: rest => push (frame.choice program) (handoff program rest)

/-! ## Step simulation -/

private theorem push_cons (argument : Value) (equation : Equation Head Value)
    (others : List (Equation Head Value)) (stack : List (Choice Head Value)) :
    push ⟨argument, equation :: others⟩ stack =
      ⟨argument, equation :: others⟩ :: stack := by
  simp [push]

/-- A step of a call with an untried occurrence is the step equation search
takes from the handoff. -/
theorem producerStep_simulates_unfinished (program : Program Head Value)
    {frame : Frame Head Value} {rest next : List (Frame Head Value)}
    {emitted : Option Value} {equation : Equation Head Value}
    (lookup : (program frame.head)[frame.next]? = some equation)
    (step : producerStep program (frame :: rest) = some (emitted, next)) :
    searchStep program (handoff program (frame :: rest)) =
      some (emitted, handoff program next) := by
  rcases frame with ⟨head, argument, ordinal⟩
  obtain ⟨inside, found⟩ := List.getElem?_eq_some_iff.mp lookup
  have unfolded : (program head).drop ordinal =
      equation :: (program head).drop (ordinal + 1) := by
    rw [List.drop_eq_getElem_cons inside, found]
  have top : handoff program (⟨head, argument, ordinal⟩ :: rest) =
      ⟨argument, equation :: (program head).drop (ordinal + 1)⟩ ::
        handoff program rest := by
    simp only [handoff, Frame.choice]
    rw [unfolded, push_cons]
  rw [top]
  cases outcome : equation argument with
  | none =>
      simp only [producerStep, lookup, outcome, Option.some.injEq,
        Prod.mk.injEq] at step
      obtain ⟨rfl, rfl⟩ := step
      simp [searchStep, outcome, handoff, Frame.choice]
  | some result =>
      cases result with
      | answer value =>
          simp only [producerStep, lookup, outcome, Option.some.injEq,
            Prod.mk.injEq] at step
          obtain ⟨rfl, rfl⟩ := step
          simp [searchStep, outcome, handoff, Frame.choice]
      | call callee callArgument =>
          by_cases more : ordinal + 1 < (program head).length
          · simp only [producerStep, lookup, outcome, more, if_true,
              Option.some.injEq, Prod.mk.injEq] at step
            obtain ⟨rfl, rfl⟩ := step
            simp [searchStep, outcome, handoff, Frame.choice]
          · simp only [producerStep, lookup, outcome, more, if_false,
              Option.some.injEq, Prod.mk.injEq] at step
            obtain ⟨rfl, rfl⟩ := step
            have last : (program head).drop (ordinal + 1) = [] :=
              List.drop_eq_nil_of_le (Nat.le_of_not_lt more)
            simp [searchStep, outcome, handoff, Frame.choice, push, last]

/-- Each producer step is a silent retirement that leaves the handoff
unchanged, or the step equation search takes from the handoff. -/
theorem producerStep_simulates (program : Program Head Value)
    {frames next : List (Frame Head Value)} {emitted : Option Value}
    (step : producerStep program frames = some (emitted, next)) :
    (emitted = none ∧ handoff program next = handoff program frames) ∨
      searchStep program (handoff program frames) =
        some (emitted, handoff program next) := by
  cases frames with
  | nil => simp [producerStep] at step
  | cons frame rest =>
      cases lookup : (program frame.head)[frame.next]? with
      | none =>
          simp only [producerStep, lookup, Option.some.injEq,
            Prod.mk.injEq] at step
          obtain ⟨rfl, rfl⟩ := step
          left
          have finished : (program frame.head).drop frame.next = [] :=
            List.drop_eq_nil_of_le (List.getElem?_eq_none_iff.mp lookup)
          refine ⟨rfl, ?_⟩
          simp [handoff, Frame.choice, push, finished]
      | some equation =>
          exact Or.inr (producerStep_simulates_unfinished program lookup step)

/-- A call with an untried occurrence always takes a step. -/
theorem producerStep_unfinished_isSome (program : Program Head Value)
    {frame : Frame Head Value} {rest : List (Frame Head Value)}
    {equation : Equation Head Value}
    (lookup : (program frame.head)[frame.next]? = some equation) :
    (producerStep program (frame :: rest)).isSome := by
  simp only [producerStep, lookup]
  split
  · rfl
  · rfl
  · split <;> rfl

/-! ## Whole runs -/

/-- The producer's answers from a frontier are equation search's answers from
its handoff. -/
theorem producerRun_sound (program : Program Head Value)
    {frames finish : List (Frame Head Value)} {answers : List Value}
    (run : ProducerRun program frames answers finish) :
    SearchRun program (handoff program frames) answers
      (handoff program finish) := by
  induction run with
  | stop frames => exact .stop _
  | step step _ ih =>
      rcases producerStep_simulates program step with ⟨rfl, same⟩ | search
      · simpa [same] using ih
      · exact .step search ih

theorem ProducerRun.append {program : Program Head Value}
    {start middle finish : List (Frame Head Value)} {first second : List Value}
    (left : ProducerRun program start first middle)
    (right : ProducerRun program middle second finish) :
    ProducerRun program start (first ++ second) finish := by
  induction left with
  | stop => simpa using right
  | step step _ ih =>
      simpa [List.append_assoc] using ProducerRun.step step (ih right)

/-- Retiring finished calls reaches a frontier whose innermost call has an
untried occurrence, without an answer and without changing the handoff. -/
theorem settle (program : Program Head Value) :
    ∀ frames : List (Frame Head Value),
      ∃ settled, ProducerRun program frames [] settled ∧
        handoff program settled = handoff program frames ∧
        (settled = [] ∨ ∃ frame rest equation, settled = frame :: rest ∧
          (program frame.head)[frame.next]? = some equation)
  | [] => ⟨[], .stop _, rfl, Or.inl rfl⟩
  | frame :: rest => by
      cases lookup : (program frame.head)[frame.next]? with
      | some equation =>
          exact ⟨frame :: rest, .stop _, rfl,
            Or.inr ⟨frame, rest, equation, rfl, lookup⟩⟩
      | none =>
          obtain ⟨settled, run, same, shape⟩ := settle program rest
          have finished : (program frame.head).drop frame.next = [] :=
            List.drop_eq_nil_of_le (List.getElem?_eq_none_iff.mp lookup)
          have retire : producerStep program (frame :: rest) = some (none, rest) := by
            simp [producerStep, lookup]
          refine ⟨settled, ?_, ?_, shape⟩
          · simpa using ProducerRun.step retire run
          · rw [same]
            simp [handoff, Frame.choice, push, finished]

/-- Every answer sequence of equation search from a handoff is one the
producer yields from its frontier. -/
theorem producerRun_complete (program : Program Head Value)
    {frames : List (Frame Head Value)} {answers : List Value}
    {finish : List (Choice Head Value)}
    (run : SearchRun program (handoff program frames) answers finish) :
    ∃ last, ProducerRun program frames answers last ∧
      handoff program last = finish := by
  generalize start : handoff program frames = stack at run
  induction run generalizing frames with
  | stop stack => exact ⟨frames, .stop _, start⟩
  | @step stack next finish emitted answers searched _ ih =>
      obtain ⟨settled, retired, same, shape⟩ := settle program frames
      rcases shape with rfl | ⟨frame, rest, equation, rfl, lookup⟩
      · rw [← start, ← same] at searched
        simp [handoff, searchStep] at searched
      · obtain ⟨⟨emitted', after⟩, stepped⟩ := Option.isSome_iff_exists.mp
          (producerStep_unfinished_isSome program (rest := rest) lookup)
        have search := producerStep_simulates_unfinished program lookup stepped
        rw [same, start, searched] at search
        simp only [Option.some.injEq, Prod.mk.injEq] at search
        obtain ⟨rfl, rest_eq⟩ := search
        obtain ⟨last, run, handed⟩ := ih rest_eq.symm
        exact ⟨last, by
          simpa using retired.append (ProducerRun.step stepped run), handed⟩

/-! ## Changes between answers -/

/-- Equation search whose program may change between segments: each segment
runs under the program in force for it. -/
inductive HistoryRun : List (Program Head Value) →
    List (Choice Head Value) → List Value → List (Choice Head Value) → Prop
  | nil (stack : List (Choice Head Value)) : HistoryRun [] stack [] stack
  | cons {program : Program Head Value} {programs : List (Program Head Value)}
      {stack middle finish : List (Choice Head Value)}
      {segment rest : List Value} :
      SearchRun program stack segment middle →
      HistoryRun programs middle rest finish →
      HistoryRun (program :: programs) stack (segment ++ rest) finish

/-- A producer run while the program in force is the one it was compiled
from, followed by equation search from its handoff under any later history,
yields the answers of equation search under the whole history. -/
theorem validated_producer_exact {compiled current : Program Head Value}
    {programs : List (Program Head Value)}
    {frames middle : List (Frame Head Value)}
    {finish : List (Choice Head Value)} {segment rest : List Value}
    (unchanged : current = compiled)
    (producer : ProducerRun compiled frames segment middle)
    (later : HistoryRun programs (handoff compiled middle) rest finish) :
    HistoryRun (current :: programs) (handoff compiled frames)
      (segment ++ rest) finish := by
  subst unchanged
  exact .cons (producerRun_sound current producer) later

/-! ## Examples -/

section Examples

/-- `pick`: the first element, or `pick` of the tail. -/
def pickProgram : Program Unit (List Nat) := fun _ =>
  [fun list => match list with
      | x :: _ => some (.answer [x])
      | [] => none,
   fun list => match list with
      | _ :: y :: ys => some (.call () (y :: ys))
      | _ => none]

/-- Run a machine for `fuel` steps and collect its answers. -/
def collect {State : Type} (step : State → Option (Option (List Nat) × State)) :
    Nat → State → List (List Nat)
  | 0, _ => []
  | fuel + 1, state =>
      match step state with
      | none => []
      | some (emitted, next) => emitted.toList ++ collect step fuel next

example : collect (producerStep pickProgram) 20 [⟨(), [1, 2, 3], 0⟩] =
    [[1], [2], [3]] := by decide

example : collect (searchStep pickProgram) 20
      (handoff pickProgram [⟨(), [1, 2, 3], 0⟩]) =
    [[1], [2], [3]] := by decide

/-- A caller that still has an alternative must stay on the frontier: a
producer that let every call replace its caller would lose that answer. -/
def descendProgram : Program Unit (List Nat) := fun _ =>
  [fun list => match list with
      | _ :: rest => some (.call () rest)
      | [] => none,
   fun list => some (.answer list)]

def replacingStep (program : Program Unit (List Nat)) :
    List (Frame Unit (List Nat)) →
      Option (Option (List Nat) × List (Frame Unit (List Nat)))
  | [] => none
  | frame :: rest =>
      match (program frame.head)[frame.next]? with
      | none => some (none, rest)
      | some equation =>
          match equation frame.argument with
          | none => some (none, { frame with next := frame.next + 1 } :: rest)
          | some (.answer value) =>
              some (some value, { frame with next := frame.next + 1 } :: rest)
          | some (.call head argument) => some (none, ⟨head, argument, 0⟩ :: rest)

example : collect (producerStep descendProgram) 20 [⟨(), [1, 2], 0⟩] =
    [[], [2], [1, 2]] := by decide

example : collect (replacingStep descendProgram) 20 [⟨(), [1, 2], 0⟩] ≠
    collect (producerStep descendProgram) 20 [⟨(), [1, 2], 0⟩] := by decide

/-- After the first answer an equation is added.  Equation search from the
handoff gives the new equation to the later calls; a producer that went on
under its compiled program would not. -/
def extendedPickProgram : Program Unit (List Nat) := fun _ =>
  pickProgram () ++ [fun _ => some (.answer [100])]

theorem unvalidated_producer_misses_new_equation :
    collect (searchStep extendedPickProgram) 20
        (handoff pickProgram [⟨(), [1, 2, 3], 1⟩]) ≠
      collect (producerStep pickProgram) 20 [⟨(), [1, 2, 3], 1⟩] := by
  decide

example : collect (searchStep extendedPickProgram) 20
    (handoff pickProgram [⟨(), [1, 2, 3], 1⟩]) =
    [[2], [3], [100], [100]] := by decide

end Examples

end Mettapedia.Languages.MeTTa.AnswerProducerHandoff
