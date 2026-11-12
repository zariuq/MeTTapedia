import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.EventMultiplicity
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Interface
import Mathlib.Logic.Equiv.Basic

/-!
# Event-indexed execution and actual transform runs

An event choice is an admitted native candidate. The finite executions of
this system are in bijection with the existing dependent runs, retaining their
complete firing word and endpoint. This bridge makes no C refinement claim.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Step

universe uO uT uH uOcc uS uF uA

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {X : Frames Tm Hom} {O : Type uOcc} [DecidableEq O]
  {State : Type uS} {Firing : State → Type uF} {Action : Type uA}
  (P : Step X O State Firing) (read : ∀ {state : State}, Firing state → Action)

def eventSystem : EventMultiplicity.System State Action where
  Choice state := {firing : Firing state // P.Admits firing}
  next _ choice := P.result choice.val choice.property
  action _ choice := read choice.val

def runOfExecution : ∀ {count : Nat} {state : State}, (P.eventSystem read).Execution count state → P.Run state
  | 0, _, _ => .nil _
  | _ + 1, _, ⟨choice, rest⟩ => .cons choice.val choice.property (runOfExecution rest)

def executionOfRun : {state : State} → P.Run state →
    (count : Nat) × (P.eventSystem read).Execution count state
  | _, .nil _ => ⟨0, PUnit.unit⟩
  | _, .cons firing admitted rest =>
      let ⟨count, tail⟩ := executionOfRun rest
      ⟨count + 1, ⟨⟨firing, admitted⟩, tail⟩⟩

theorem runOfExecution_executionOfRun : ∀ {state : State} (run : P.Run state),
    P.runOfExecution read (P.executionOfRun read run).2 = run
  | _, .nil _ => rfl
  | _, .cons firing admitted rest => by
      have ih := runOfExecution_executionOfRun rest
      rw [executionOfRun]
      generalize decoded_eq : P.executionOfRun read rest = decoded at *
      rcases decoded with ⟨count, tail⟩
      change Step.Run.cons firing admitted (P.runOfExecution read tail) = _
      rw [ih]

theorem executionOfRun_runOfExecution : ∀ {count : Nat} {state : State}
    (run : (P.eventSystem read).Execution count state),
    P.executionOfRun read (P.runOfExecution read run) = ⟨count, run⟩
  | 0, _, run => by cases run; rfl
  | _ + 1, _, ⟨choice, rest⟩ => by
      rw [runOfExecution, executionOfRun, executionOfRun_runOfExecution]
      rfl

def executionRunEquiv (state : State) :
    ((count : Nat) × (P.eventSystem read).Execution count state) ≃ P.Run state where
  toFun run := P.runOfExecution read run.2
  invFun := P.executionOfRun read
  left_inv run := by
    rcases run with ⟨count, run⟩
    exact P.executionOfRun_runOfExecution read run
  right_inv := P.runOfExecution_executionOfRun read

theorem runOfExecution_word : ∀ {count : Nat} {state : State}
    (run : (P.eventSystem read).Execution count state),
    (P.runOfExecution read run).word.map (fun entry => read entry.2) = (P.eventSystem read).word run
  | 0, _, _ => rfl
  | _ + 1, _, ⟨choice, rest⟩ =>
      congrArg (List.cons (read choice.val)) (runOfExecution_word rest)

theorem runOfExecution_length {count : Nat} {state : State}
    (run : (P.eventSystem read).Execution count state) : (P.runOfExecution read run).word.length = count := by
  have words := P.runOfExecution_word read run
  have lengths := congrArg List.length words
  simpa only [List.length_map, EventMultiplicity.System.word_length] using lengths

theorem runOfExecution_last : ∀ {count : Nat} {state : State}
    (run : (P.eventSystem read).Execution count state),
    (P.runOfExecution read run).last = (P.eventSystem read).last run
  | 0, _, _ => rfl
  | _ + 1, _, ⟨_, rest⟩ => runOfExecution_last rest

/-- Restriction of the complete run equivalence to one exact event count. -/
def countedExecutionRunEquiv (state : State) (count : Nat) :
    (P.eventSystem read).Execution count state ≃ {run : P.Run state // run.word.length = count} :=
  (Equiv.sigmaSubtype (β := fun count => (P.eventSystem read).Execution count state) count).symm.trans
    ((P.executionRunEquiv read state).subtypeEquiv
      (p := fun run => run.1 = count) (q := fun run => run.word.length = count)
      (fun run => by
        change run.1 = count ↔ (P.runOfExecution read run.2).word.length = count
        rw [runOfExecution_length]))

theorem countedExecutionRunEquiv_apply (state : State) (count : Nat)
    (run : (P.eventSystem read).Execution count state) :
    (P.countedExecutionRunEquiv read state count run).val = P.runOfExecution read run := rfl

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Step
