import Mathlib.Data.List.Basic

/-!
# Control-flow admission for permission transitions

The control language is parametric in states, actions and their partial
transition function. Conditions are nondeterministic. A loop is admitted when
every non-returning outcome restores its entry state, so admission covers any
finite number of iterations. A failed permission operation is an explicit
fault in the execution relation, not silently excluded from the semantics.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.CMemory.PermissionFlow

universe u v

inductive Plan (Action : Type u) where
  | done
  | step (action : Action) (next : Plan Action)
  | ret
  | breakLoop
  | continueLoop
  | branch (yes no next : Plan Action)
  | loop (body next : Plan Action)
  deriving DecidableEq, Repr, BEq, ReflBEq, LawfulBEq

inductive ExitKind where
  | normal | returned | broke | continued | fault
  deriving DecidableEq, Repr, BEq, ReflBEq, LawfulBEq

structure Exit (State : Type v) where
  kind : ExitKind
  state : State
  deriving DecidableEq, Repr, BEq, ReflBEq, LawfulBEq

variable {State : Type v} {Action : Type u}

def continueExits (run : State → Option (List (Exit State))) :
    List (Exit State) → Option (List (Exit State))
  | [] => some []
  | first :: rest =>
      (if first.kind == .normal then run first.state else some [first]).bind fun before =>
      (continueExits run rest).bind fun after => some (before ++ after)

def check [BEq State] [LawfulBEq State] (transition : State → Action → Option State)
    (returnAllowed : State → Bool) : Plan Action → State → Option (List (Exit State))
  | .done, s => some [⟨.normal, s⟩]
  | .step action next, s => (transition s action).bind fun after =>
      check transition returnAllowed next after
  | .ret, s => if returnAllowed s then some [⟨.returned, s⟩] else none
  | .breakLoop, s => some [⟨.broke, s⟩]
  | .continueLoop, s => some [⟨.continued, s⟩]
  | .branch yes no next, s => do
      let left ← check transition returnAllowed yes s
      let right ← check transition returnAllowed no s
      continueExits (check transition returnAllowed next) (left ++ right).eraseDups
  | .loop body next, s => do
      let iterations ← check transition returnAllowed body s
      if iterations.all (fun exit => exit.kind == .returned || exit.state == s) then
        let after ← check transition returnAllowed next s
        pure (iterations.filter (fun exit => exit.kind == .returned) ++ after)
      else none

inductive Execution (transition : State → Action → Option State) :
    Plan Action → State → Exit State → Prop where
  | done (s : State) : Execution transition .done s ⟨.normal, s⟩
  | step {s after : State} {action : Action} {next : Plan Action} {outcome : Exit State}
      (enabled : transition s action = some after)
      (rest : Execution transition next after outcome) :
      Execution transition (.step action next) s outcome
  | failed {s : State} {action : Action} {next : Plan Action}
      (disabled : transition s action = none) :
      Execution transition (.step action next) s ⟨.fault, s⟩
  | ret (s : State) : Execution transition .ret s ⟨.returned, s⟩
  | breakLoop (s : State) : Execution transition .breakLoop s ⟨.broke, s⟩
  | continueLoop (s : State) : Execution transition .continueLoop s ⟨.continued, s⟩
  | branchNormal {yes no next : Plan Action} {s after : State} {outcome : Exit State}
      (choice : Bool)
      (branch : Execution transition (if choice then yes else no) s ⟨.normal, after⟩)
      (rest : Execution transition next after outcome) :
      Execution transition (.branch yes no next) s outcome
  | branchAbrupt {yes no next : Plan Action} {s : State} {outcome : Exit State}
      (choice : Bool) (branch : Execution transition (if choice then yes else no) s outcome)
      (abrupt : outcome.kind ≠ .normal) :
      Execution transition (.branch yes no next) s outcome
  | loopStop {body next : Plan Action} {s : State} {outcome : Exit State}
      (rest : Execution transition next s outcome) :
      Execution transition (.loop body next) s outcome
  | loopBreak {body next : Plan Action} {s after : State} {outcome : Exit State}
      (iteration : Execution transition body s ⟨.broke, after⟩)
      (rest : Execution transition next after outcome) :
      Execution transition (.loop body next) s outcome
  | loopAbrupt {body next : Plan Action} {s : State} {outcome : Exit State}
      (iteration : Execution transition body s outcome)
      (abrupt : outcome.kind = .returned ∨ outcome.kind = .fault) :
      Execution transition (.loop body next) s outcome
  | loopAgain {body next : Plan Action} {s : State} {iterationExit outcome : Exit State}
      (iteration : Execution transition body s iterationExit)
      (repeats : iterationExit.kind = .normal ∨ iterationExit.kind = .continued)
      (rest : Execution transition (.loop body next) iterationExit.state outcome) :
      Execution transition (.loop body next) s outcome

theorem continue_cons {run : State → Option (List (Exit State))}
    {first : Exit State} {rest outputs : List (Exit State)}
    (accepted : continueExits run (first :: rest) = some outputs) :
    ∃ before after,
      (if first.kind == .normal then run first.state else some [first]) = some before ∧
      continueExits run rest = some after ∧ outputs = before ++ after := by
  obtain ⟨before, hfirst, rest⟩ := Option.bind_eq_some_iff.mp accepted
  obtain ⟨after, hrest, same⟩ := Option.bind_eq_some_iff.mp rest
  exact ⟨before, after, hfirst, hrest, (Option.some.inj same).symm⟩

theorem continue_normal {run : State → Option (List (Exit State))}
    {inputs outputs : List (Exit State)}
    (accepted : continueExits run inputs = some outputs)
    {state : State} (member : Exit.mk .normal state ∈ inputs) :
    ∃ next, run state = some next ∧ ∀ exit ∈ next, exit ∈ outputs := by
  induction inputs generalizing outputs with
  | nil => simp at member
  | cons first rest ih =>
      obtain ⟨before, after, hfirst, hrest, rfl⟩ := continue_cons accepted
      rcases List.mem_cons.mp member with same | later
      · subst first
        exact ⟨before, by simpa using hfirst, fun _ present => List.mem_append_left _ present⟩
      · obtain ⟨next, checked, included⟩ := ih hrest later
        exact ⟨next, checked, fun exit present => List.mem_append_right _ (included exit present)⟩

theorem continue_abrupt {run : State → Option (List (Exit State))}
    {inputs outputs : List (Exit State)}
    (accepted : continueExits run inputs = some outputs) {exit : Exit State}
    (member : exit ∈ inputs) (abrupt : exit.kind ≠ .normal) : exit ∈ outputs := by
  induction inputs generalizing outputs with
  | nil => simp at member
  | cons first rest ih =>
      obtain ⟨before, after, hfirst, hrest, rfl⟩ := continue_cons accepted
      rcases List.mem_cons.mp member with same | later
      · subst first
        have same : before = [exit] := by simpa [abrupt] using hfirst.symm
        subst before
        exact List.mem_append_left _ (by simp)
      · exact List.mem_append_right _ (ih hrest later)

variable [BEq State] [LawfulBEq State] {transition : State → Action → Option State}
    {returnAllowed : State → Bool}

theorem check_branch {yes no next : Plan Action} {s : State} {outputs : List (Exit State)}
    (accepted : check transition returnAllowed (.branch yes no next) s = some outputs) :
    ∃ left right, check transition returnAllowed yes s = some left ∧
      check transition returnAllowed no s = some right ∧
      continueExits (check transition returnAllowed next) (left ++ right).eraseDups = some outputs := by
  obtain ⟨left, hleft, rest⟩ := Option.bind_eq_some_iff.mp accepted
  obtain ⟨right, hright, combined⟩ := Option.bind_eq_some_iff.mp rest
  exact ⟨left, right, hleft, hright, combined⟩

theorem check_loop {body next : Plan Action} {s : State} {outputs : List (Exit State)}
    (accepted : check transition returnAllowed (.loop body next) s = some outputs) :
    ∃ iterations after, check transition returnAllowed body s = some iterations ∧
      (∀ exit ∈ iterations, exit.kind = .returned ∨ exit.state = s) ∧
      check transition returnAllowed next s = some after ∧
      outputs = iterations.filter (fun exit => exit.kind == .returned) ++ after := by
  obtain ⟨iterations, hbody, tail⟩ := Option.bind_eq_some_iff.mp accepted
  change (if _ then _ else none) = some outputs at tail
  split at tail
  next invariant =>
    obtain ⟨after, hnext, same⟩ := Option.bind_eq_some_iff.mp tail
    exact ⟨iterations, after, hbody,
      by simpa only [List.all_eq_true, Bool.or_eq_true, beq_iff_eq] using invariant,
      hnext, (Option.some.inj same).symm⟩
  next => simp at tail

omit [BEq State] [LawfulBEq State] in
theorem continue_property {run : State → Option (List (Exit State))}
    {inputs outputs : List (Exit State)} {property : Exit State → Prop}
    (accepted : continueExits run inputs = some outputs)
    (initial : ∀ exit ∈ inputs, property exit)
    (continuation : ∀ state next, run state = some next → ∀ exit ∈ next, property exit) :
    ∀ exit ∈ outputs, property exit := by
  induction inputs generalizing outputs with
  | nil => simp [continueExits] at accepted; subst outputs; simp
  | cons first rest ih =>
      obtain ⟨before, after, hfirst, hrest, rfl⟩ := continue_cons accepted
      intro exit member
      rcases List.mem_append.mp member with early | late
      · by_cases normal : first.kind = .normal
        · exact continuation first.state before (by simpa [normal] using hfirst) exit early
        · have same : before = [first] := by simpa [normal] using hfirst.symm
          rw [same] at early
          have equal := List.mem_singleton.mp early
          subst exit
          exact initial first (by simp)
      · exact ih hrest (fun outcome present => initial outcome (by simp [present])) exit late

theorem checked_outcomes_no_fault {plan : Plan Action} {state : State}
    {outputs : List (Exit State)}
    (accepted : check transition returnAllowed plan state = some outputs) :
    ∀ exit ∈ outputs, exit.kind ≠ .fault := by
  induction plan generalizing state outputs with
  | done => simp [check] at accepted; subst outputs; simp
  | step action next ih =>
      obtain ⟨after, _, rest⟩ := Option.bind_eq_some_iff.mp accepted
      exact ih rest
  | ret =>
      simp only [check] at accepted
      split at accepted
      · simp only [Option.some.injEq] at accepted; subst outputs; simp
      · simp at accepted
  | breakLoop | continueLoop => simp [check] at accepted; subst outputs; simp
  | branch yes no next ihyes ihno ihnext =>
      obtain ⟨left, right, hleft, hright, combined⟩ := check_branch accepted
      exact continue_property (property := fun exit => exit.kind ≠ .fault) combined
        (by
          intro exit present
          rcases List.mem_append.mp (List.mem_eraseDups.mp present) with h | h
          · exact ihyes hleft exit h
          · exact ihno hright exit h)
        (by intro state next checked; exact ihnext checked)
  | loop body next ihbody ihnext =>
      obtain ⟨iterations, after, hbody, _, hnext, rfl⟩ := check_loop accepted
      intro exit present
      rcases List.mem_append.mp present with h | h
      · exact ihbody hbody exit (List.mem_filter.mp h).1
      · exact ihnext hnext exit h

/-- Every finite execution of an admitted program is represented among the
checked outcomes, including executions attempting an undefined operation. -/
theorem covers_execution {plan : Plan Action} {state : State} {outcome : Exit State}
    (execution : Execution transition plan state outcome) {outputs : List (Exit State)}
    (accepted : check transition returnAllowed plan state = some outputs) : outcome ∈ outputs := by
  induction execution generalizing outputs with
  | done => simp only [check, Option.some.injEq] at accepted; subst outputs; simp
  | step enabled rest ih =>
      obtain ⟨after, enabled', checked⟩ := Option.bind_eq_some_iff.mp accepted
      have same := Option.some.inj (enabled.symm.trans enabled')
      subst after
      exact ih checked
  | failed disabled => simp [check, disabled] at accepted
  | ret =>
      simp only [check] at accepted
      split at accepted
      · simp only [Option.some.injEq] at accepted; subst outputs; simp
      · simp at accepted
  | breakLoop => simp only [check, Option.some.injEq] at accepted; subst outputs; simp
  | continueLoop => simp only [check, Option.some.injEq] at accepted; subst outputs; simp
  | @branchNormal yes no next s after outcome choice branch rest ihbranch ihrest =>
      obtain ⟨left, right, hleft, hright, combined⟩ := check_branch accepted
      have member : Exit.mk .normal after ∈ left ++ right := by
        cases choice with
        | false => exact List.mem_append_right _ (ihbranch hright)
        | true => exact List.mem_append_left _ (ihbranch hleft)
      obtain ⟨next, checked, included⟩ := continue_normal combined (List.mem_eraseDups.mpr member)
      exact included _ (ihrest checked)
  | branchAbrupt choice branch abrupt ihbranch =>
      obtain ⟨left, right, hleft, hright, combined⟩ := check_branch accepted
      apply continue_abrupt combined _ abrupt
      apply List.mem_eraseDups.mpr
      cases choice with
      | false => exact List.mem_append_right _ (ihbranch hright)
      | true => exact List.mem_append_left _ (ihbranch hleft)
  | loopStop rest ih =>
      obtain ⟨_, _, _, _, hnext, same⟩ := check_loop accepted
      rw [same]; exact List.mem_append_right _ (ih hnext)
  | loopBreak iteration rest ihiteration ihrest =>
      obtain ⟨iterations, after, hbody, invariant, hnext, same⟩ := check_loop accepted
      have equal : _ = _ := (invariant _ (ihiteration hbody)).resolve_left (by simp)
      subst equal
      rw [same]; exact List.mem_append_right _ (ihrest hnext)
  | loopAbrupt iteration abrupt ih =>
      obtain ⟨iterations, after, hbody, invariant, hnext, same⟩ := check_loop accepted
      have member := ih hbody
      rcases abrupt with returned | fault
      · rw [same]; exact List.mem_append_left _ (List.mem_filter.mpr ⟨member, by simp [returned]⟩)
      · exact False.elim (checked_outcomes_no_fault hbody _ member fault)
  | @loopAgain body next s iterationExit outcome iteration repeats rest ihiteration ihrest =>
      obtain ⟨iterations, after, hbody, invariant, hnext, same⟩ := check_loop accepted
      have different : iterationExit.kind ≠ ExitKind.returned := by rcases repeats with h | h <;> simp [h]
      have equal := (invariant _ (ihiteration hbody)).resolve_left different
      exact ihrest (by simpa [equal] using accepted)

/-- Undefined permission operations are impossible along any finite execution
of an admitted program; the result includes all branches and loop iterations. -/
theorem admitted_no_fault {plan : Plan Action} {state : State} {outcome : Exit State}
    (accepted : ∃ outputs, check transition returnAllowed plan state = some outputs)
    (execution : Execution transition plan state outcome) : outcome.kind ≠ .fault := by
  obtain ⟨outputs, checked⟩ := accepted
  exact checked_outcomes_no_fault checked outcome (covers_execution execution checked)

/-- Every return of an admitted plan satisfies its cleanup/transfer contract. -/
theorem checked_returns {plan : Plan Action} {state : State} {outputs : List (Exit State)}
    (accepted : check transition returnAllowed plan state = some outputs) :
    ∀ exit ∈ outputs, exit.kind = .returned → returnAllowed exit.state = true := by
  induction plan generalizing state outputs with
  | done => simp [check] at accepted; subst outputs; simp
  | step action next ih =>
      obtain ⟨after, _, rest⟩ := Option.bind_eq_some_iff.mp accepted
      exact ih rest
  | ret =>
      simp only [check] at accepted
      split at accepted
      · simp only [Option.some.injEq] at accepted; subst outputs
        intro exit present _
        have := List.mem_singleton.mp present
        subst exit
        assumption
      · simp at accepted
  | breakLoop | continueLoop => simp [check] at accepted; subst outputs; simp
  | branch yes no next ihyes ihno ihnext =>
      obtain ⟨left, right, hleft, hright, combined⟩ := check_branch accepted
      exact continue_property
        (property := fun exit => exit.kind = .returned → returnAllowed exit.state = true) combined
        (by
          intro exit present
          rcases List.mem_append.mp (List.mem_eraseDups.mp present) with h | h
          · exact ihyes hleft exit h
          · exact ihno hright exit h)
        (by intro state next checked; exact ihnext checked)
  | loop body next ihbody ihnext =>
      obtain ⟨iterations, after, hbody, _, hnext, rfl⟩ := check_loop accepted
      intro exit present
      rcases List.mem_append.mp present with h | h
      · exact ihbody hbody exit (List.mem_filter.mp h).1
      · exact ihnext hnext exit h

omit [BEq State] [LawfulBEq State] in
theorem Execution.invariant {property : State → Prop}
    (preserved : ∀ s a after, transition s a = some after → property s → property after)
    {plan : Plan Action} {state : State} {outcome : Exit State}
    (execution : Execution transition plan state outcome) (initial : property state) :
    property outcome.state := by
  induction execution with
  | done | failed | ret | breakLoop | continueLoop => exact initial
  | step enabled rest ih => exact ih (preserved _ _ _ enabled initial)
  | branchNormal choice branch rest ihbranch ihrest => exact ihrest (ihbranch initial)
  | branchAbrupt choice branch abrupt ih => exact ih initial
  | loopStop rest ih => exact ih initial
  | loopBreak iteration rest ihiteration ihrest => exact ihrest (ihiteration initial)
  | loopAbrupt iteration abrupt ih => exact ih initial
  | loopAgain iteration repeats rest ihiteration ihrest => exact ihrest (ihiteration initial)

/-- A reachable intermediate state, before cleanup may discharge the last
permission. Completed subplans use the same execution relation as admission;
returned/faulted branches cannot resume their enclosing continuation. -/
inductive Prefix (transition : State → Action → Option State) :
    Plan Action → State → State → Prop where
  | start (plan : Plan Action) (s : State) : Prefix transition plan s s
  | step {s after reached : State} {action : Action} {next : Plan Action}
      (enabled : transition s action = some after)
      (rest : Prefix transition next after reached) :
      Prefix transition (.step action next) s reached
  | branchHere {yes no next : Plan Action} {s reached : State} (choice : Bool)
      (inside : Prefix transition (if choice then yes else no) s reached) :
      Prefix transition (.branch yes no next) s reached
  | branchNext {yes no next : Plan Action} {s after reached : State} (choice : Bool)
      (finished : Execution transition (if choice then yes else no) s ⟨.normal, after⟩)
      (rest : Prefix transition next after reached) :
      Prefix transition (.branch yes no next) s reached
  | loopHere {body next : Plan Action} {s reached : State}
      (inside : Prefix transition body s reached) : Prefix transition (.loop body next) s reached
  | loopStop {body next : Plan Action} {s reached : State}
      (rest : Prefix transition next s reached) : Prefix transition (.loop body next) s reached
  | loopBreak {body next : Plan Action} {s after reached : State}
      (finished : Execution transition body s ⟨.broke, after⟩)
      (rest : Prefix transition next after reached) : Prefix transition (.loop body next) s reached
  | loopAgain {body next : Plan Action} {s reached : State} {iteration : Exit State}
      (finished : Execution transition body s iteration)
      (repeats : iteration.kind = .normal ∨ iteration.kind = .continued)
      (rest : Prefix transition (.loop body next) iteration.state reached) :
      Prefix transition (.loop body next) s reached

omit [BEq State] [LawfulBEq State] in
theorem Prefix.invariant {property : State → Prop}
    (preserved : ∀ s a after, transition s a = some after → property s → property after)
    {plan : Plan Action} {state reached : State}
    (path : Prefix transition plan state reached) (initial : property state) : property reached := by
  induction path with
  | start => exact initial
  | step enabled rest ih => exact ih (preserved _ _ _ enabled initial)
  | branchHere choice inside ih => exact ih initial
  | branchNext choice finished rest ih => exact ih (finished.invariant preserved initial)
  | loopHere inside ih => exact ih initial
  | loopStop rest ih => exact ih initial
  | loopBreak finished rest ih => exact ih (finished.invariant preserved initial)
  | loopAgain finished repeats rest ih => exact ih (finished.invariant preserved initial)

end Mettapedia.Machines.CMemory.PermissionFlow
