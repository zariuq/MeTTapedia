import Mettapedia.Machines.CMemory.PermissionFlow

/-!
# Mandatory first iterations in permission plans

`resumeIteration` composes one already checked body with its latch or break
continuation. A body return/fault stays terminal. Nested loops keep their own
break and continue targets. This is a lowering of Cesta's permission plans,
not an interpreter for C scalar expressions or machine execution.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.CMemory.PermissionFlow

universe u v

def resume {Action : Type u} (body normal continued broken : Plan Action) : Plan Action :=
  match body with
  | .done => normal
  | .step action next => .step action (resume next normal continued broken)
  | .ret => .ret
  | .breakLoop => broken
  | .continueLoop => continued
  | .branch yes no next =>
      let tail := resume next normal continued broken
      .branch (resume yes tail continued broken) (resume no tail continued broken) .done
  | .loop body next => .loop body (resume next normal continued broken)

def resumeIteration {Action : Type u} (body finish broken : Plan Action) : Plan Action :=
  resume body finish finish broken

variable {State : Type v} {Action : Type u} {transition : State → Action → Option State}

inductive IterationResume (transition : State → Action → Option State)
    (normal continued broken : Plan Action) : Exit State → Exit State → Prop where
  | normal {state : State} {outcome : Exit State}
      (run : Execution transition normal state outcome) :
      IterationResume transition normal continued broken ⟨.normal, state⟩ outcome
  | continued {state : State} {outcome : Exit State}
      (run : Execution transition continued state outcome) :
      IterationResume transition normal continued broken ⟨.continued, state⟩ outcome
  | broke {state : State} {outcome : Exit State}
      (run : Execution transition broken state outcome) :
      IterationResume transition normal continued broken ⟨.broke, state⟩ outcome
  | terminal {outcome : Exit State}
      (terminal : outcome.kind = .returned ∨ outcome.kind = .fault) :
      IterationResume transition normal continued broken outcome outcome

private theorem choose_done {yes no : Plan Action} {choice : Bool}
    {state : State} {outcome : Exit State}
    (run : Execution transition (if choice then yes else no) state outcome) :
    Execution transition (.branch yes no .done) state outcome := by
  by_cases normal : outcome.kind = .normal
  · obtain ⟨kind, after⟩ := outcome
    dsimp at normal
    subst kind
    exact .branchNormal choice run (.done after)
  · exact .branchAbrupt choice run normal

/-- A mandatory body precedes its selected continuation. A continue skips
ordinary branch tails; nested loops keep their own transfer targets. -/
theorem resume_execution {body normal continued broken : Plan Action} {state : State}
    {iteration outcome : Exit State} (run : Execution transition body state iteration)
    (follow : IterationResume transition normal continued broken iteration outcome) :
    Execution transition (resume body normal continued broken) state outcome := by
  induction run generalizing normal continued broken outcome with
  | done =>
      cases follow with
      | normal run => exact run
      | terminal h => simp at h
  | step enabled rest ih => exact .step enabled (ih follow)
  | failed disabled => cases follow with | terminal _ => exact .failed disabled
  | ret => cases follow with | terminal _ => exact .ret _
  | breakLoop =>
      cases follow with
      | broke run => exact run
      | terminal h => simp at h
  | continueLoop =>
      cases follow with
      | continued run => exact run
      | terminal h => simp at h
  | branchNormal choice branch rest ihbranch ihrest =>
      apply choose_done (choice := choice)
      cases choice <;> simp only [Bool.false_eq_true, ↓reduceIte] at *
      all_goals exact ihbranch (.normal (ihrest follow))
  | branchAbrupt choice branch abrupt ih =>
      apply choose_done (choice := choice)
      cases choice <;> simp only [Bool.false_eq_true, ↓reduceIte] at *
      all_goals cases follow with
      | normal _ => exact False.elim (abrupt rfl)
      | continued run => exact ih (.continued run)
      | broke run => exact ih (.broke run)
      | terminal h => exact ih (.terminal h)
  | loopStop rest ih => exact .loopStop (ih follow)
  | loopBreak iteration rest ihiteration ihrest => exact .loopBreak iteration (ihrest follow)
  | loopAbrupt iteration abrupt ih =>
      cases follow with
      | normal _ => simp at abrupt
      | continued _ => simp at abrupt
      | broke _ => simp at abrupt
      | terminal _ => exact .loopAbrupt iteration abrupt
  | loopAgain iteration repeats rest ihiteration ihrest =>
      exact .loopAgain iteration repeats (ihrest follow)

theorem mandatory_no_fault [BEq State] [LawfulBEq State]
    {body finish broken : Plan Action} {state : State} {returnAllowed : State → Bool}
    {outputs : List (Exit State)} {iteration outcome : Exit State}
    (admitted : check transition returnAllowed (resumeIteration body finish broken) state = some outputs)
    (bodyRun : Execution transition body state iteration)
    (continuation : IterationResume transition finish finish broken iteration outcome) :
    outcome.kind ≠ .fault := by
  exact admitted_no_fault ⟨outputs, admitted⟩ (resume_execution bodyRun continuation)

theorem mandatory_returns [BEq State] [LawfulBEq State]
    {body finish broken : Plan Action} {state : State} {returnAllowed : State → Bool}
    {outputs : List (Exit State)} {iteration : Exit State} {after : State}
    (admitted : check transition returnAllowed (resumeIteration body finish broken) state = some outputs)
    (bodyRun : Execution transition body state iteration)
    (continuation : IterationResume transition finish finish broken iteration ⟨.returned, after⟩) :
    returnAllowed after = true := by
  exact checked_returns admitted _ (covers_execution (resume_execution bodyRun continuation) admitted) rfl

namespace Controls

private def mark (state : List Nat) (event : Nat) : Option (List Nat) := some (state ++ [event])
private def doneAfter (event : Nat) : Plan Nat := .step event .ret

-- Continue skips the rest of its branch and reaches the latch exactly once.
example : check mark (fun _ => true)
    (resumeIteration (.branch .continueLoop (.step 2 .done) (.step 77 .done))
      (doneAfter 1) (doneAfter 3)) [] =
    some [⟨.returned, [1]⟩, ⟨.returned, [2, 77, 1]⟩] := by decide

-- Break bypasses the condition/repeat continuation.
example : check mark (fun _ => true)
    (resumeIteration .breakLoop (doneAfter 1) (doneAfter 3)) [] =
    some [⟨.returned, [3]⟩] := by decide

-- The mandatory body cannot be replaced by an optional zero-iteration path.
example : check mark (fun _ => true)
    (resumeIteration (.step 7 .done) .ret .ret) [] =
    some [⟨.returned, [7]⟩] := by decide

private def refused (_ : Nat) (_ : Unit) : Option Nat := none
example : check refused (fun _ => true)
    (resumeIteration (.step () .done) .ret .ret) 0 = none := by decide

end Controls

end Mettapedia.Machines.CMemory.PermissionFlow
