import Mettapedia.GSLT.LanguageDef.CompiledRecursiveAnswerProducer

/-!
# Answer producers whose bodies resume after a call

`CompiledRecursiveAnswerProducer` covers relations whose every alternative
emits one answer or continues with a last call.  A body that computes with a
call's answer, such as `(Cons $y (perm $ys))` or a `let` over a generator,
needs more: after each answer of the call the body resumes where it stopped,
from the same state.  Here a body is

* an answer;
* no answer;
* a call whose every answer resumes a continuation of the body;
* a last call, whose answers are the body's.

`Body.bind` sequences a body into a continuation.  Its answers are the list
monad's bind of the body's answers (`answers_bind`), which is what binding each
operand of a nested call, in evaluation order, before its consumer denotes.  A
call resumed by `answer` has the answers of a last call (`answers_call_answer`),
which licenses entering a last call in its caller's place.

`collect?` runs such a producer depth first over a frontier of bodies, each
with the stack of continuations its answers resume.  When a collection
completes, its answers are exactly the denotation of the frontier, in order and
with multiplicity (`collect?_exact`).  The recursive producer of
`CompiledRecursiveAnswerProducer` embeds with the same denotation
(`embedDenotation`), so the extension is conservative.

`Expr` gives source bodies in the order the executor evaluates them: an
operand before its consumer, a left operand before a right one, a condition
before its branch, a bound expression before its pattern.  Lowering such a body
into continuations keeps its answers and their order (`Expr.lower_answers`), so
a machine whose equations are lowered this way denotes, for every call, the
answers of its source equations in order (`lowered_denotation`).

Binding operands in another order changes the answer order
(`operand_order_matters`), so a lowering must bind in evaluation order; an
exhausted collection is not an empty one (`exhausted_collection_is_not_zero`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.CompiledContinuationAnswerProducer

open Mettapedia.GSLT.Dynamics.AnswerEffects

universe u v

/-- A lowered body over call states `State` and answers `Answer`. -/
inductive Body (State : Type u) (Answer : Type v) : Type (max u v) where
  | answer (value : Answer)
  | fail
  | call (state : State) (resume : Answer → Body State Answer)
  | tail (state : State)

namespace Body

variable {State : Type u} {Answer : Type v}

/-- The answers of a body, given the answers of every call. -/
def answers (value : State → List Answer) : Body State Answer → List Answer
  | answer a => [a]
  | fail => []
  | call state resume => (value state).flatMap fun a => answers value (resume a)
  | tail state => value state

/-- Run a body, then the continuation on each of its answers. -/
def bind : Body State Answer → (Answer → Body State Answer) → Body State Answer
  | answer a, next => next a
  | fail, _ => fail
  | call state resume, next => call state fun a => bind (resume a) next
  | tail state, next => call state next

theorem answers_bind (value : State → List Answer) (body : Body State Answer)
    (next : Answer → Body State Answer) :
    (body.bind next).answers value =
      (body.answers value).flatMap fun a => (next a).answers value := by
  induction body with
  | answer a => simp [bind, answers]
  | fail => simp [bind, answers]
  | call state resume ih => simp [bind, answers, ih, List.flatMap_assoc]
  | tail state => simp [bind, answers]

/-- A call resumed by `answer` answers as a last call does. -/
theorem answers_call_answer (value : State → List Answer) (state : State) :
    (call state answer : Body State Answer).answers value =
      (tail state : Body State Answer).answers value := by
  simp [answers]

end Body

/-- Each call state's alternatives, in source order. -/
structure Machine (State : Type u) (Answer : Type v) where
  branches : State → List (Body State Answer)

variable {State : Type u} {Answer : Type v}

/-- A completed denotation solves the unfolding of every call. -/
structure Denotation (machine : Machine State Answer) where
  value : State → List Answer
  unfold : ∀ state,
    value state = (machine.branches state).flatMap (Body.answers value)

/-- A frontier entry: an answer already reached, or a body running under the
stack of continuations its answers resume, innermost first. -/
inductive Residual (State : Type u) (Answer : Type v) : Type (max u v) where
  | yield (answer : Answer)
  | run (body : Body State Answer) (pending : List (Answer → Body State Answer))

/-- The answers an answer becomes once the pending continuations have run. -/
def pendingAnswers (value : State → List Answer) :
    List (Answer → Body State Answer) → Answer → List Answer
  | [], a => [a]
  | next :: rest, a =>
      ((next a).answers value).flatMap (pendingAnswers value rest)

/-- The ordered answers a frontier denotes. -/
def frontierValue (value : State → List Answer) :
    List (Residual State Answer) → List Answer
  | [] => []
  | .yield a :: rest => a :: frontierValue value rest
  | .run body pending :: rest =>
      (body.answers value).flatMap (pendingAnswers value pending) ++
        frontierValue value rest

theorem frontierValue_append (value : State → List Answer)
    (left right : List (Residual State Answer)) :
    frontierValue value (left ++ right) =
      frontierValue value left ++ frontierValue value right := by
  induction left with
  | nil => rfl
  | cons entry rest ih =>
      cases entry <;> simp [frontierValue, ih, List.append_assoc]

theorem frontierValue_runs (value : State → List Answer)
    (bodies : List (Body State Answer))
    (pending : List (Answer → Body State Answer)) :
    frontierValue value (bodies.map fun body => .run body pending) =
      bodies.flatMap fun body =>
        (body.answers value).flatMap (pendingAnswers value pending) := by
  induction bodies with
  | nil => rfl
  | cons body rest ih => simp [frontierValue, ih]

/-- Depth-first collection of a frontier within `fuel` steps.  No answer is
published unless the whole frontier completes. -/
def collect? (machine : Machine State Answer) :
    Nat → List (Residual State Answer) → Option (List Answer)
  | 0, _ => none
  | _ + 1, [] => some []
  | fuel + 1, .yield a :: rest => (collect? machine fuel rest).map (a :: ·)
  | fuel + 1, .run (.answer a) [] :: rest =>
      collect? machine fuel (.yield a :: rest)
  | fuel + 1, .run (.answer a) (next :: pending) :: rest =>
      collect? machine fuel (.run (next a) pending :: rest)
  | fuel + 1, .run .fail _ :: rest => collect? machine fuel rest
  | fuel + 1, .run (.call state resume) pending :: rest =>
      collect? machine fuel
        ((machine.branches state).map (fun body => .run body (resume :: pending)) ++
          rest)
  | fuel + 1, .run (.tail state) pending :: rest =>
      collect? machine fuel
        ((machine.branches state).map (fun body => .run body pending) ++ rest)

/-- A completed collection yields exactly the frontier's denotation, in order
and with multiplicity. -/
theorem collect?_exact (machine : Machine State Answer)
    (denotation : Denotation machine) (fuel : Nat)
    (frontier : List (Residual State Answer)) (answers : List Answer)
    (completed : collect? machine fuel frontier = some answers) :
    answers = frontierValue denotation.value frontier := by
  induction fuel generalizing frontier answers with
  | zero => simp [collect?] at completed
  | succ fuel ih =>
      match frontier, completed with
      | [], completed =>
          simp [collect?] at completed
          simp [frontierValue, completed]
      | .yield a :: rest, completed =>
          cases equation : collect? machine fuel rest with
          | none => simp [collect?, equation] at completed
          | some tail =>
              have exactAnswers : a :: tail = answers := by
                simpa [collect?, equation] using completed
              subst answers
              simp [frontierValue, ih rest tail equation]
      | .run (.answer a) [] :: rest, completed =>
          rw [ih _ _ completed]
          simp [frontierValue, Body.answers, pendingAnswers]
      | .run (.answer a) (next :: pending) :: rest, completed =>
          rw [ih _ _ completed]
          simp [frontierValue, Body.answers, pendingAnswers]
      | .run .fail pending :: rest, completed =>
          rw [ih _ _ completed]
          simp [frontierValue, Body.answers]
      | .run (.call state resume) pending :: rest, completed =>
          rw [ih _ _ completed, frontierValue_append, frontierValue_runs]
          simp only [frontierValue, Body.answers, denotation.unfold state,
            List.flatMap_assoc, pendingAnswers]
      | .run (.tail state) pending :: rest, completed =>
          rw [ih _ _ completed, frontierValue_append, frontierValue_runs]
          simp only [frontierValue, Body.answers, denotation.unfold state,
            List.flatMap_assoc]

/-- The answers of a call collected from scratch. -/
theorem collect?_call_exact (machine : Machine State Answer)
    (denotation : Denotation machine) (fuel : Nat) (state : State)
    (answers : List Answer)
    (completed : collect? machine fuel [.run (.tail state) []] = some answers) :
    answers = denotation.value state := by
  rw [collect?_exact machine denotation fuel _ answers completed]
  simp [frontierValue, Body.answers, pendingAnswers]

theorem exhausted_collection_is_not_zero (machine : Machine State Answer)
    (frontier : List (Residual State Answer)) :
    collect? machine 0 frontier ≠ some [] := by
  simp [collect?]

/-! ## The recursive producer is the case without continuations -/

section Embedding

open CompiledRecursiveAnswerProducer in
/-- An emitted answer, or a last call. -/
def embedBranch : Branch State Answer → Body State Answer
  | .answer a => .answer a
  | .tail state => .tail state

open CompiledRecursiveAnswerProducer in
def embedMachine (machine : CompiledRecursiveAnswerProducer.Machine State Answer) :
    Machine State Answer where
  branches state := (machine.branches state).map embedBranch

open CompiledRecursiveAnswerProducer in
theorem foldBranches_list_eq (value : State → List Answer)
    (branches : List (Branch State Answer)) :
    foldBranches listEffect value branches =
      (branches.map embedBranch).flatMap (Body.answers value) := by
  induction branches with
  | nil => rfl
  | cons branch rest ih =>
      cases branch with
      | answer a =>
          show List.append [a] (foldBranches listEffect value rest) = _
          rw [ih]
          simp [embedBranch, Body.answers]
      | tail state =>
          show List.append (value state) (foldBranches listEffect value rest) = _
          rw [ih]
          simp [embedBranch, Body.answers]

open CompiledRecursiveAnswerProducer in
/-- A completed list denotation of a recursive producer is one of its
embedding, so every recursive producer theorem is a special case here. -/
def embedDenotation
    {machine : CompiledRecursiveAnswerProducer.Machine State Answer}
    (denotation : CompiledRecursiveAnswerProducer.Denotation machine listEffect) :
    Denotation (embedMachine machine) where
  value := denotation.value
  unfold state := (denotation.unfold state).trans (foldBranches_list_eq _ _)

end Embedding

/-! ## Lowering source bodies in evaluation order -/

section Lowering

/-- Source bodies as the executor evaluates them: an operand's answers are
reached before its consumer's, a left operand before a right one, a
condition before its branch, and a bound expression before its pattern. -/
inductive Expr (State : Type u) (Answer : Type v) : Type (max u v) where
  | value (a : Answer)
  | zero
  | call (operand : Expr State Answer) (state : Answer → State)
  | combine (left right : Expr State Answer) (join : Answer → Answer → Answer)
  | branch (condition : Expr State Answer) (truth : Answer → Bool)
      (yes no : Expr State Answer)
  | bind (bound : Expr State Answer) (accepts : Answer → Bool)
      (body : Answer → Expr State Answer)

namespace Expr

/-- The answers of a source body, as equation search reaches them. -/
def eval (value : State → List Answer) : Expr State Answer → List Answer
  | Expr.value a => [a]
  | zero => []
  | call operand state =>
      (eval value operand).flatMap fun a => value (state a)
  | combine left right join =>
      (eval value left).flatMap fun a =>
        (eval value right).flatMap fun b => [join a b]
  | branch condition truth yes no =>
      (eval value condition).flatMap fun a =>
        if truth a then eval value yes else eval value no
  | bind bound accepts body =>
      (eval value bound).flatMap fun a =>
        if accepts a then eval value (body a) else []

/-- Lower a source body, continuing with `next` on each of its answers. -/
def lower : Expr State Answer → (Answer → Body State Answer) → Body State Answer
  | Expr.value a, next => next a
  | zero, _ => .fail
  | call operand state, next => lower operand fun a => .call (state a) next
  | combine left right join, next =>
      lower left fun a => lower right fun b => next (join a b)
  | branch condition truth yes no, next =>
      lower condition fun a => if truth a then lower yes next else lower no next
  | bind bound accepts body, next =>
      lower bound fun a => if accepts a then lower (body a) next else .fail

/-- Lowering in evaluation order keeps the answers and their order. -/
theorem lower_answers (value : State → List Answer) (expr : Expr State Answer)
    (next : Answer → Body State Answer) :
    (expr.lower next).answers value =
      (expr.eval value).flatMap fun a => (next a).answers value := by
  induction expr generalizing next with
  | value a => simp [lower, eval]
  | zero => simp [lower, eval, Body.answers]
  | call operand state ih =>
      simp [lower, eval, ih, Body.answers, List.flatMap_assoc]
  | combine left right join ihLeft ihRight =>
      simp [lower, eval, ihLeft, ihRight, List.flatMap_assoc]
  | branch condition truth yes no ihCondition ihYes ihNo =>
      rw [lower, ihCondition, eval, List.flatMap_assoc]
      congr 1
      funext a
      by_cases holds : truth a <;> simp [holds, ihYes, ihNo]
  | bind bound accepts body ihBound ihBody =>
      rw [lower, ihBound, eval, List.flatMap_assoc]
      congr 1
      funext a
      by_cases holds : accepts a <;> simp [holds, ihBody, Body.answers]

/-- A body lowered to answer directly has the source body's answers. -/
theorem lower_answer (value : State → List Answer) (expr : Expr State Answer) :
    (expr.lower .answer).answers value = expr.eval value := by
  rw [lower_answers]
  simp [Body.answers]

end Expr

/-- A machine whose equations are lowered from source bodies denotes, for
each call, the answers of its source equations in order. -/
theorem lowered_denotation (machine : Machine State Answer)
    (denotation : Denotation machine)
    (source : State → List (Expr State Answer))
    (lowered : ∀ state,
      machine.branches state = (source state).map fun expr => expr.lower .answer)
    (state : State) :
    denotation.value state =
      (source state).flatMap (Expr.eval denotation.value) := by
  rw [denotation.unfold state, lowered state, List.flatMap_map]
  congr 1
  funext expr
  exact Expr.lower_answer denotation.value expr

end Lowering

/-! ## Operand order -/

section Examples

inductive Coin | heads | tails
  deriving DecidableEq, Repr

/-- One call state, a coin; answers are sequences of coins. -/
def coinMachine : Machine Unit (List Coin) where
  branches _ := [.answer [.heads], .answer [.tails]]

/-- Two tosses, the left operand bound first, as the executor evaluates. -/
def tossLeftFirst : Body Unit (List Coin) :=
  .call () fun left => .call () fun right => .answer (left ++ right)

/-- The same tosses with the right operand bound first. -/
def tossRightFirst : Body Unit (List Coin) :=
  .call () fun right => .call () fun left => .answer (left ++ right)

theorem toss_left_first :
    collect? coinMachine 64 [.run tossLeftFirst []] =
      some [[.heads, .heads], [.heads, .tails],
            [.tails, .heads], [.tails, .tails]] := by
  decide

/-- Binding the operands in another order changes the answer order. -/
theorem operand_order_matters :
    collect? coinMachine 64 [.run tossRightFirst []] ≠
      collect? coinMachine 64 [.run tossLeftFirst []] := by
  decide

end Examples

end Mettapedia.GSLT.LanguageDef.CompiledContinuationAnswerProducer
