import Mettapedia.GSLT.Dynamics.ContextualEffectHandlers

/-!
# Qualified removal and reuse of contextual computations

At an already demanded site, duplicating a computation and reusing its first
result are different programs in the existing effect syntax. Read-only
programs with no choice or intent admit both reuse and discarding under the
isolated-world evaluator's complete observation: ordered occurrences, branch
paths, final state and intents. The proofs are uniform in the continuation.

Controls separate nondeterministic correlation, occurrence multiplicity,
state updates and intent duplication. This is not a full CBPV calculus, a
call-by-need implementation, a cost theorem, or a divergence theorem. In
particular, this evaluator does not record the cost of a read.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dynamics.ContextualStrategyQualification

open ContextualEffectHandlers

universe u

variable {State Answer Result Intent : Type u}

/-- An effect restriction of the actual program, not an assumed equality of
the two proposed executions. Every state-dependent branch must qualify. -/
inductive ReadOnly : Program State Answer Intent → Prop where
  | pure (answer : Answer) : ReadOnly (.pure answer)
  | read (next : State → Program State Answer Intent) :
      (∀ state, ReadOnly (next state)) → ReadOnly (.read next)

/-- Execute twice before passing both answers to the continuation. -/
def repeatThen (program : Program State Answer Intent)
    (next : Answer → Answer → Program State Result Intent) : Program State Result Intent :=
  program.bind fun first => program.bind fun second => next first second

/-- Execute once at this demanded site and reuse the returned value. -/
def reuseThen (program : Program State Answer Intent)
    (next : Answer → Answer → Program State Result Intent) : Program State Result Intent :=
  program.bind fun answer => next answer answer

/-- A qualifying read-only computation has one answer at the given state,
with no change to any subsequent continuation's complete world observation. -/
theorem readOnly_bind (program : Program State Answer Intent) (qualified : ReadOnly program)
    (state : State) :
    ∃ answer, ∀ {Result : Type u} (next : Answer → Program State Result Intent)
      (branch : BranchTrace),
      runWorldsAt (program.bind next) state branch = runWorldsAt (next answer) state branch := by
  induction qualified with
  | pure answer => exact ⟨answer, fun _ _ => rfl⟩
  | read next _ ih =>
      obtain ⟨answer, replay⟩ := ih state
      exact ⟨answer, fun continuation branch => replay continuation branch⟩

/-- Reuse is valid before every effectful continuation, not merely for a
chosen pure result. The complete ordered world result is preserved. -/
theorem repeat_eq_reuse (program : Program State Answer Intent) (qualified : ReadOnly program)
    (next : Answer → Answer → Program State Result Intent) (state : State)
    (branch : BranchTrace) :
    runWorldsAt (repeatThen program next) state branch =
      runWorldsAt (reuseThen program next) state branch := by
  obtain ⟨answer, replay⟩ := readOnly_bind program qualified state
  unfold repeatThen reuseThen
  rw [replay, replay, replay]

/-- Discarding an unused qualifying computation preserves the observation.
This is not an erasure theorem for writes, intents, choice or divergence. -/
theorem discard_readOnly (program : Program State Answer Intent) (qualified : ReadOnly program)
    (next : Program State Result Intent) (state : State) (branch : BranchTrace) :
    runWorldsAt (program.bind fun _ => next) state branch = runWorldsAt next state branch := by
  obtain ⟨_, replay⟩ := readOnly_bind program qualified state
  exact replay (fun _ => next) branch

namespace Canary

/-- Two actual state reads, with no intervening write or external intent. -/
def readTwice : Program Nat Nat Bool :=
  .read fun first => .read fun second => .pure (first + second)

theorem readTwice_qualified : ReadOnly readTwice :=
  .read _ fun _ => .read _ fun _ => .pure _

/-- The consumer itself writes state and emits an intent; these effects are
not disallowed or erased by the theorem's restriction on the earlier program. -/
def effectfulConsumer (first second : Nat) : Program Nat (Nat × Nat) Bool :=
  .write (first + second) (.intent true (.pure (first, second)))

theorem reuse_before_effectful_consumer (state : Nat) :
    runWorlds (repeatThen readTwice effectfulConsumer) state =
      runWorlds (reuseThen readTwice effectfulConsumer) state :=
  repeat_eq_reuse readTwice readTwice_qualified effectfulConsumer state []

def choice : Program Unit Bool Unit := .choose (.pure false) (.pure true)

def pair (first second : Bool) : Program Unit (Bool × Bool) Unit := .pure (first, second)

theorem repeated_choice_independent :
    (runWorlds (repeatThen choice pair) ()).map WorldResult.answer =
      [(false, false), (false, true), (true, false), (true, true)] := rfl

theorem reused_choice_correlated :
    (runWorlds (reuseThen choice pair) ()).map WorldResult.answer =
      [(false, false), (true, true)] := rfl

theorem unqualified_choice_reuse_changes_answers :
    (runWorlds (repeatThen choice pair) ()).map WorldResult.answer ≠
      (runWorlds (reuseThen choice pair) ()).map WorldResult.answer := by decide

/-- Even agreement on every answer value is weaker than occurrence agreement. -/
def duplicateChoice : Program Unit Bool Unit := .choose (.pure false) (.pure false)

theorem same_answer_support (answer : Bool × Bool) :
    answer ∈ (runWorlds (repeatThen duplicateChoice pair) ()).map WorldResult.answer ↔
      answer ∈ (runWorlds (reuseThen duplicateChoice pair) ()).map WorldResult.answer := by
  simp [repeatThen, reuseThen, duplicateChoice, pair, Program.bind, runWorlds, runWorldsAt]

theorem different_occurrence_counts :
    (runWorlds (repeatThen duplicateChoice pair) ()).length = 4 ∧
      (runWorlds (reuseThen duplicateChoice pair) ()).length = 2 := ⟨rfl, rfl⟩

theorem increment_reuse_changes_state_and_answer :
    (runWorlds (repeatThen ContextualEffectHandlers.Canary.incrementOnce
      (fun first second => .pure (first, second))) 0).map
      (fun result => (result.answer, result.state)) = [((0, 1), 2)] ∧
    (runWorlds (reuseThen ContextualEffectHandlers.Canary.incrementOnce
      (fun first second => .pure (first, second))) 0).map
      (fun result => (result.answer, result.state)) = [((0, 0), 1)] := ⟨rfl, rfl⟩

def intentOnce : Program Unit Unit Bool := .intent true (.pure ())

theorem intent_reuse_changes_requests :
    (runWorlds (repeatThen intentOnce (fun _ _ => .pure ())) ()).map WorldResult.intents =
      [[true, true]] ∧
    (runWorlds (reuseThen intentOnce (fun _ _ => .pure ())) ()).map WorldResult.intents =
      [[true]] := ⟨rfl, rfl⟩

theorem discarding_unused_write_changes_state :
    (runWorlds ((.write 1 (.pure ()) : Program Nat Unit Bool).bind fun _ => .pure 7) 0).map
      (fun result => (result.answer, result.state)) = [(7, 1)] ∧
    (runWorlds (.pure 7 : Program Nat Nat Bool) 0).map
      (fun result => (result.answer, result.state)) = [(7, 0)] := ⟨rfl, rfl⟩

end Canary

#print axioms readOnly_bind
#print axioms repeat_eq_reuse
#print axioms discard_readOnly
#print axioms Canary.reuse_before_effectful_consumer
#print axioms Canary.unqualified_choice_reuse_changes_answers
#print axioms Canary.same_answer_support
#print axioms Canary.different_occurrence_counts
#print axioms Canary.increment_reuse_changes_state_and_answer
#print axioms Canary.intent_reuse_changes_requests
#print axioms Canary.discarding_unused_write_changes_state

end Mettapedia.GSLT.Dynamics.ContextualStrategyQualification
