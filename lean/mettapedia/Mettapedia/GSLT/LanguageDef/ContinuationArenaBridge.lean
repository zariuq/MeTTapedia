import Mettapedia.GSLT.LanguageDef.CompiledContinuationAnswerProducer
import Mettapedia.GSLT.Dynamics.ContinuationRegionSwitching

/-!
# From lowered answer bodies to incremental shared continuations

The already defined continuation-body calculus supplies the control operations
of the generic machine. The conservation law retains an emitted prefix and the
denotation of its entire residual frontier. Thus the shared arena is connected
to the existing source-body lowering theorem, rather than justified only by a
new reference machine written beside it.

Continuation functions in this bridge are semantic closures. A native compiler
must realize them with its finite resume labels and capture maps. The generic
machine also accepts first-order frame data, as the transfer controls exhibit.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ContinuationArenaBridge

open CompiledContinuationAnswerProducer
open Mettapedia.Machines.SharedContinuation
open Mettapedia.GSLT.Dynamics
open ContextIndexedSwitching (repeats)

variable {Call Answer : Type}

abbrev Frame (Call Answer : Type) := Answer → Body Call Answer
abbrev Reference (Call Answer : Type) :=
  State Unit (Body Call Answer) (Frame Call Answer) Answer

def program (machine : Machine Call Answer) :
    Program Unit (Body Call Answer) Call (Frame Call Answer) Answer where
  inspect
    | .answer value => .ret value
    | .fail => .fail
    | .call state resume => .call state resume
    | .tail state => .tail state
  branches _ call := (machine.branches call).map ((), ·)
  resume _ frame answer := ((), frame answer)

def residuals (tasks : List (Task Unit (Body Call Answer) (Frame Call Answer))) :
    List (Residual Call Answer) :=
  tasks.map fun task => .run task.control task.returns

/-- The exact ordered observations still owed, preceded by those delivered. -/
def balance (value : Call → List Answer) (state : Reference Call Answer) : List Answer :=
  state.emitted.map Prod.snd ++ frontierValue value (residuals state.frontier)

theorem balance_step (machine : Machine Call Answer) (denotation : Denotation machine)
    (state : Reference Call Answer) :
    balance denotation.value (step (program machine) state) = balance denotation.value state := by
  rcases state with ⟨frontier, emitted⟩
  cases frontier with
  | nil => rfl
  | cons task rest =>
      rcases task with ⟨context, body, pending⟩
      cases body with
      | answer answer =>
          cases pending with
          | nil => simp [step, program, balance, residuals, frontierValue,
              Body.answers, pendingAnswers, List.append_assoc]
          | cons next pending => simp [step, program, balance, residuals, frontierValue,
              Body.answers, pendingAnswers]
      | fail => simp [step, program, balance, residuals, frontierValue, Body.answers]
      | call call resume =>
          simp only [step, program, balance, residuals, List.map_cons, List.map_append,
            List.map_map, Function.comp_def]
          rw [frontierValue_append, frontierValue_runs]
          simp [frontierValue, Body.answers, denotation.unfold call,
            List.flatMap_assoc, pendingAnswers]
      | tail call =>
          simp only [step, program, balance, residuals, List.map_cons, List.map_append,
            List.map_map, Function.comp_def]
          rw [frontierValue_append, frontierValue_runs]
          simp [frontierValue, Body.answers, denotation.unfold call, List.flatMap_assoc]

theorem balance_steps (machine : Machine Call Answer) (denotation : Denotation machine)
    (count : Nat) (state : Reference Call Answer) :
    balance denotation.value (repeats (step (program machine)) count state) =
      balance denotation.value state := by
  induction count generalizing state with
  | zero => rfl
  | succ count ih => rw [repeats, ih, balance_step]

/-- Incremental shared execution is conservative over the existing body
semantics, without waiting for the frontier to finish. -/
theorem shared_balance (machine : Machine Call Answer) (denotation : Denotation machine)
    (count : Nat) (state : Reference Call Answer) :
    balance denotation.value
      (repeats (checkedStep (program machine)) count (encode state)).1.decode =
        balance denotation.value state := by
  rw [ContinuationRegionSwitching.decode_steps, decode_encode, balance_steps]

def initial (call : Call) : Reference Call Answer := ⟨[⟨(), .tail call, []⟩], []⟩

/-- Exhaustion after any number of transferred shared steps yields exactly
the source denotation. Fuel exhaustion is not a premise of this theorem. -/
theorem completed_answers (machine : Machine Call Answer) (denotation : Denotation machine)
    (count : Nat) (call : Call)
    (exhausted : (repeats (checkedStep (program machine)) count (encode (initial call))).1.frontier = []) :
    (repeats (checkedStep (program machine)) count (encode (initial call))).1.emitted.map Prod.snd =
      denotation.value call := by
  have conserved := shared_balance machine denotation count (initial call)
  simp only [balance, ArenaState.decode, exhausted, List.map_nil, residuals,
    frontierValue, List.append_nil] at conserved
  simpa [initial, frontierValue, Body.answers, pendingAnswers] using conserved

end Mettapedia.GSLT.LanguageDef.ContinuationArenaBridge
