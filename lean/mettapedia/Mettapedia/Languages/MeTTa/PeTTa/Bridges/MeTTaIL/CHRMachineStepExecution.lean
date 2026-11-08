import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CHRMachineStoreExecution

/-! The CHR machine source executes as `Mettapedia.Languages.CHR.Machine`:
machine states, the start state, introduction and goals. -/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CHRMachineExecution

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst)
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Mettapedia.Languages.MeTTa.PeTTa.Eval
open Mettapedia.Languages.MeTTa.PeTTa.BridgeKit
open WireKit StrictCallKit CHRMachineSource
open Mettapedia.Languages.CHR (Value Term Environment IntOperator IntExpr Comparison ArithmeticFault Guard
  guardsEval Head Goal Rule)
open Mettapedia.Languages.CHR.Machine (Key Occ Store Pick At Table slot put without alive removePicks ids
  occurrencesOf instantiateTerms)

abbrev MachineTask := Mettapedia.Languages.CHR.Machine.Task
abbrev MachineStatus := Mettapedia.Languages.CHR.Machine.Status
abbrev MachineState := Mettapedia.Languages.CHR.Machine.State
abbrev MachineFrame := Mettapedia.Languages.CHR.Machine.Frame

/-! ## Machine states -/

def frameAtom (frame : MachineFrame) : Atom :=
  .expression [.symbol "ChrFrame", integer frame.index, listAtom (frame.heads.map headAtom),
    occsAtom frame.candidates, environmentAtom frame.environment, picksAtom frame.picks, idsAtom frame.used]

def taskAtom : MachineTask → Atom
  | .seeds heads => .expression [.symbol "ChrSeeds", listAtom (heads.map headAtom)]
  | .goals environment goals =>
    .expression [.symbol "ChrGoals", environmentAtom environment, listAtom (goals.map goalAtom)]
  | .scan active key values remaining =>
    .expression [.symbol "ChrScan", integer active, keyAtom key, valuesAtom values,
      listAtom (remaining.map atAtom)]
  | .search active key values occurrence after frames =>
    .expression [.symbol "ChrSearch", integer active, keyAtom key, valuesAtom values, atAtom occurrence,
      listAtom (after.map atAtom), listAtom (frames.map frameAtom)]

def tasksAtom (tasks : List MachineTask) : Atom := listAtom (tasks.map taskAtom)

def statusAtom : MachineStatus → Atom
  | .running => .symbol "ChrRunning"
  | .failed => .symbol "ChrFailed"
  | .faulted reason => .expression [.symbol "ChrFaulted", faultAtom reason]

def firedAtom (key : Mettapedia.Languages.CHR.Key) : Atom :=
  .expression [.symbol "ChrFired", integer key.rule, idsAtom key.heads]

def historyAtom (history : List Mettapedia.Languages.CHR.Key) : Atom := listAtom (history.map firedAtom)

def stateAtom (state : MachineState) : Atom :=
  .expression [.symbol "ChrState", tasksAtom state.tasks, storeAtom state.store, historyAtom state.history,
    integer state.next, statusAtom state.status, idsAtom state.seeds]

def programAtom (table : Table) : Atom := .expression [.symbol "ChrProgram", tableAtom table]

/-- The atoms the machine's case selections read. -/
scoped syntax "state_case " term (" unfolding" " [" term,* "]")? : tactic
macro_rules
  | `(tactic| state_case $scrutinee $[unfolding [$extra,*]]?) => do
    let extra := (extra.map (·.getElems)).getD #[]
    `(tactic| machine_case $scrutinee unfolding [stateAtom, tasksAtom, taskAtom, frameAtom, statusAtom, historyAtom,
      firedAtom, programAtom, tableAtom, storeAtom, slotAtom, occsAtom, occAtom, keyAtom, picksAtom, pickAtom,
      idsAtom, headAtom, goalAtom, ruleAtom, atAtom, guardAtom, expressionAtom, faultAtom, exceptAtom, pairAtom,
      Mettapedia.Languages.ProcessCalculi.MORK.applySubst, $extra,*])

/-! ## Start and status -/

theorem start_returns (caller : Subst) (state : State) (code : Atom) (seeds : List Head)
    (one : Returns caller state code (listAtom (seeds.map headAtom))) :
    Returns caller state (apply "gslt:chr-machine:start" [code])
      (stateAtom (Mettapedia.Languages.CHR.Machine.start seeds)) := by
  machine_call (.cons one .nil)
  simp only [stateAtom, Mettapedia.Languages.CHR.Machine.start, tasksAtom, List.map, listAtom, taskAtom, storeAtom,
    historyAtom, statusAtom, idsAtom, nil]
  exact make_returns _ _ "ChrState" _ _ inert
    (.cons (cons_returns _ state _ _ _ _ (make_returns _ _ "ChrSeeds" _ _ inert (.cons bound .nil))
      (Eval.symbol_returns runtime _ state _))
    (.cons (Eval.symbol_returns runtime _ state _) (.cons (Eval.symbol_returns runtime _ state _)
    (.cons (integer_returns runtime _ state 0) (.cons (Eval.symbol_returns runtime _ state _)
    (.cons (Eval.symbol_returns runtime _ state _) .nil))))))

theorem withStatus_returns (caller : Subst) (state : State) (first second : Atom) (machine : MachineState)
    (status : MachineStatus) (one : Returns caller state first (stateAtom machine))
    (two : Returns caller state second (statusAtom status)) :
    Returns caller state (apply "gslt:chr-machine:with-status" [first, second])
      (stateAtom { machine with status }) := by
  machine_call (.cons one (.cons two .nil))
  state_case (bound)
  exact make_returns _ _ "ChrState" _ _ inert (.cons bound (.cons bound (.cons bound (.cons bound
    (.cons bound (.cons bound .nil))))))

/-! ## Candidates -/

theorem candidates_returns (caller : Subst) (state : State) (codes : List Atom) (index position active : Nat)
    (values : List Value) (head : Head) (store : Store)
    (returns : List.Forall₂ (fun code value => Returns caller state code value) codes
      [integer index, integer position, integer active, valuesAtom values, headAtom head, storeAtom store]) :
    Returns caller state (apply "gslt:chr-machine:candidates" codes)
      (occsAtom (Mettapedia.Languages.CHR.Machine.candidates index position active values head store)) := by
  machine_call returns
  apply pure_if_returns _ _ _ _ (decide (integer (index : Int) = integer (position : Int))) _ _ _
    (equal_returns _ state _ _ _ _ bound bound)
  rw [integer_nat_decide]
  by_cases same : index = position
  · simp only [same, decide_true, ↓reduceIte, Mettapedia.Languages.CHR.Machine.candidates, occsAtom, List.map,
      listAtom, occAtom]
    exact cons_returns _ state _ _ _ _ (make_returns _ _ "ChrOcc" _ _ inert (.cons bound (.cons bound .nil)))
      (Eval.symbol_returns runtime _ state _)
  · simp only [same, decide_false, Bool.false_eq_true, ↓reduceIte, Mettapedia.Languages.CHR.Machine.candidates]
    state_case (bound)
    exact slot_returns state (Mettapedia.Languages.CHR.Machine.Head.key head) store _ _ _
      (make_returns _ _ "ChrKey" _ _ inert (.cons bound (.cons bound .nil))) bound

/-! ## Introduction and goals -/

theorem next_cast (next : Nat) : integer ((next + 1 : Nat) : Int) = integer ((next : Int) + 1) := by
  simp [integer]

theorem introduce_returns (caller : Subst) (state : State) (codes : List Atom) (table : Table) (head : Head)
    (environment : Environment) (resume : MachineTask) (original tail : List MachineTask) (machine : MachineState)
    (seeds : List Nat)
    (returns : List.Forall₂ (fun code value => Returns caller state code value) codes
      [programAtom table, headAtom head, environmentAtom environment, taskAtom resume, tasksAtom original,
        tasksAtom tail, storeAtom machine.store, historyAtom machine.history, integer machine.next,
        statusAtom machine.status, idsAtom seeds]) :
    Returns caller state (apply "gslt:chr-machine:introduce" codes)
      (stateAtom (Mettapedia.Languages.CHR.Machine.introduce table head environment resume original tail machine
        seeds)) := by
  machine_call returns
  state_case (bound)
  have instantiated := instantiateAll_returns state head.arguments environment
  cases found : instantiateTerms environment head.arguments with
  | none =>
    rw [found] at instantiated
    state_case (instantiated _ _ _ bound bound)
    simp only [Mettapedia.Languages.CHR.Machine.introduce, found, stateAtom, statusAtom, faultAtom, termAtom]
    exact make_returns _ _ "ChrState" _ _ inert (.cons bound (.cons bound (.cons bound (.cons bound
      (.cons (make_returns _ _ "ChrFaulted" _ _ inert (.cons (make_returns _ _ "ChrUninstantiated" _ _ inert
        (.cons (make_returns _ _ "ChrTupleTerm" _ _ inert (.cons bound .nil)) .nil)) .nil))
      (.cons bound .nil))))))
  | some values =>
    rw [found] at instantiated
    state_case (instantiated _ _ _ bound bound)
    state_case (bound)
    apply pure_let_returns _ _ _ "key" _ (keyAtom (Mettapedia.Languages.CHR.Machine.Head.key head)) _ _ (by rfl)
      (make_returns _ _ "ChrKey" _ _ inert (.cons bound (.cons bound .nil)))
    simp only [Mettapedia.Languages.CHR.Machine.introduce, found, stateAtom, tasksAtom, List.map, listAtom,
      taskAtom, next_cast]
    exact make_returns _ _ "ChrState" _ _ inert
      (.cons (cons_returns _ state _ _ _ _ (make_returns _ _ "ChrScan" _ _ inert (.cons bound (.cons bound
          (.cons bound (.cons (occurrencesOf_returns state _ table _ _ _ bound bound) .nil)))))
        (cons_returns _ state _ _ _ _ bound bound))
      (.cons (put_returns state _ _ machine.store _ _ _ _ bound
          (cons_returns _ state _ _ _ _ (make_returns _ _ "ChrOcc" _ _ inert (.cons bound (.cons bound .nil)))
            (slot_returns state _ machine.store _ _ _ bound bound)) bound)
      (.cons bound (.cons (integer_add_returns runtime _ state _ _ _ 1 bound (integer_returns runtime _ state 1))
      (.cons bound (.cons bound .nil))))))

theorem goal_returns (caller : Subst) (state : State) (codes : List Atom) (table : Table)
    (environment : Environment) (current : Goal) (goals : List Goal) (tail : List MachineTask)
    (machine : MachineState) (tasks : machine.tasks = .goals environment (current :: goals) :: tail)
    (returns : List.Forall₂ (fun code value => Returns caller state code value) codes
      [programAtom table, goalAtom current, environmentAtom environment, listAtom (goals.map goalAtom),
        tasksAtom tail, storeAtom machine.store, historyAtom machine.history, integer machine.next,
        statusAtom machine.status, idsAtom machine.seeds]) :
    Returns caller state (apply "gslt:chr-machine:goal" codes)
      (stateAtom (Mettapedia.Languages.CHR.Machine.goal table environment current goals tail machine)) := by
  machine_call returns
  cases current with
  | tell head =>
    state_case (bound)
    exact introduce_returns _ state _ table head environment (.goals environment goals)
      (.goals environment (.tell head :: goals) :: tail) tail machine machine.seeds
      (.cons bound (.cons bound (.cons bound (.cons (make_returns _ _ "ChrGoals" _ _ inert (.cons bound (.cons bound .nil)))
      (.cons (cons_returns _ state _ _ _ _ (make_returns _ _ "ChrGoals" _ _ inert
          (.cons bound (.cons (cons_returns _ state _ _ _ _ bound bound) .nil))) bound)
      (.cons bound (.cons bound (.cons bound (.cons bound (.cons bound (.cons bound .nil)))))))))))
  | assign index expression =>
    state_case (bound)
    have evaluated := eval_returns state expression environment
    cases result : expression.eval environment with
    | error reason =>
      rw [result] at evaluated
      state_case (evaluated _ _ _ bound bound)
      simp only [Mettapedia.Languages.CHR.Machine.goal, result, stateAtom, tasks, tasksAtom, List.map, listAtom,
        taskAtom, statusAtom]
      exact make_returns _ _ "ChrState" _ _ inert
        (.cons (cons_returns _ state _ _ _ _ (make_returns _ _ "ChrGoals" _ _ inert
            (.cons bound (.cons (cons_returns _ state _ _ _ _ bound bound) .nil))) bound)
        (.cons bound (.cons bound (.cons bound
        (.cons (make_returns _ _ "ChrFaulted" _ _ inert (.cons bound .nil)) (.cons bound .nil))))))
    | ok value =>
      rw [result] at evaluated
      state_case (evaluated _ _ _ bound bound)
      have looked := lookup_returns state index environment
      cases found : Mettapedia.Languages.CHR.lookup environment index with
      | none =>
        rw [found] at looked
        state_case (looked _ _ _ bound bound)
        simp only [Mettapedia.Languages.CHR.Machine.goal, result, found, stateAtom, tasksAtom, List.map,
          listAtom, taskAtom, environmentAtom, bindAtom, valueAtom]
        exact make_returns _ _ "ChrState" _ _ inert
          (.cons (cons_returns _ state _ _ _ _ (make_returns _ _ "ChrGoals" _ _ inert
              (.cons (cons_returns _ state _ _ _ _ (make_returns _ _ "ChrBind" _ _ inert
                (.cons bound (.cons bound .nil))) bound) (.cons bound .nil))) bound)
          (.cons bound (.cons bound (.cons bound (.cons bound (.cons bound .nil))))))
      | some old =>
        rw [found] at looked
        state_case (looked _ _ _ bound bound)
        apply pure_if_returns _ _ _ _ (decide (valueAtom old = valueAtom (.integer value))) _ _ _
          (equal_returns _ state _ _ _ _ bound bound)
        rw [valueAtom_decide]
        by_cases same : old = .integer value
        · simp only [same, decide_true, ↓reduceIte, Mettapedia.Languages.CHR.Machine.goal, result, found,
            stateAtom, tasksAtom, List.map, listAtom, taskAtom]
          exact make_returns _ _ "ChrState" _ _ inert
            (.cons (cons_returns _ state _ _ _ _ (make_returns _ _ "ChrGoals" _ _ inert
                (.cons bound (.cons bound .nil))) bound)
            (.cons bound (.cons bound (.cons bound (.cons bound (.cons bound .nil))))))
        · simp only [same, decide_false, Bool.false_eq_true, ↓reduceIte, Mettapedia.Languages.CHR.Machine.goal,
            result, found, stateAtom, tasks, tasksAtom, List.map, listAtom, taskAtom, statusAtom]
          exact make_returns _ _ "ChrState" _ _ inert
            (.cons (cons_returns _ state _ _ _ _ (make_returns _ _ "ChrGoals" _ _ inert
                (.cons bound (.cons (cons_returns _ state _ _ _ _ bound bound) .nil))) bound)
            (.cons bound (.cons bound (.cons bound
            (.cons (Eval.symbol_returns runtime _ state _) (.cons bound .nil))))))
  | fail =>
    state_case (bound)
    simp only [Mettapedia.Languages.CHR.Machine.goal, stateAtom, tasks, tasksAtom, List.map, listAtom, taskAtom,
      statusAtom]
    exact make_returns _ _ "ChrState" _ _ inert
      (.cons (cons_returns _ state _ _ _ _ (make_returns _ _ "ChrGoals" _ _ inert
          (.cons bound (.cons (cons_returns _ state _ _ _ _ bound bound) .nil))) bound)
      (.cons bound (.cons bound (.cons bound
      (.cons (Eval.symbol_returns runtime _ state _) (.cons bound .nil))))))

#print axioms start_returns
#print axioms introduce_returns
#print axioms goal_returns
#print axioms withStatus_returns
#print axioms candidates_returns

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CHRMachineExecution
