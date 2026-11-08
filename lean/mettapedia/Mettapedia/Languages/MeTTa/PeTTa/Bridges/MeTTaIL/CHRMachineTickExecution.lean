import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CHRMachineScanExecution
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CHRMachineSearchExecution
import Mettapedia.Languages.CHR.MachineReady

/-! The CHR machine source executes as `Mettapedia.Languages.CHR.Machine`:
one tick, a bounded run, and the package port. Over a table whose rule
occurrences have heads, from a state whose scans and searches do, the
literal source computes exactly the machine's tick and bounded run. -/

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
open Mettapedia.Languages.CHR (Value Term Environment Head Goal Rule)
open Mettapedia.Languages.CHR.Machine (Key Occ Store Pick At Table TableHeaded TaskReady Ready)

theorem tick_returns (caller : Subst) (state : State) (first second : Atom) (table : Table)
    (machine : MachineState) (ready : Ready machine)
    (one : Returns caller state first (programAtom table)) (two : Returns caller state second (stateAtom machine)) :
    Returns caller state (apply "gslt:chr-machine:tick" [first, second])
      (stateAtom (Mettapedia.Languages.CHR.Machine.tick table machine)) := by
  machine_call (.cons one (.cons two .nil))
  obtain ⟨tasks, store, history, next, status, seeds⟩ := machine
  cases status with
  | failed =>
    state_case (bound)
    exact bound
  | faulted reason =>
    state_case (bound)
    exact bound
  | running =>
    state_case (bound)
    cases tasks with
    | nil =>
      state_case (bound)
      exact bound
    | cons task tail =>
      state_case (bound)
      have taskReady : TaskReady task := ready task List.mem_cons_self
      cases task with
      | seeds heads =>
        cases heads with
        | nil =>
          state_case (bound)
          exact make_returns _ _ "ChrState" _ _ inert (.cons bound (.cons bound (.cons bound (.cons bound
            (.cons (Eval.symbol_returns runtime _ state _) (.cons bound .nil))))))
        | cons head heads =>
          state_case (bound)
          exact introduce_returns _ state _ table head [] (.seeds heads) (.seeds (head :: heads) :: tail) tail
            ⟨.seeds (head :: heads) :: tail, store, history, next, .running, seeds⟩ (next :: seeds)
            (.cons bound (.cons bound (.cons (Eval.symbol_returns runtime _ state _)
            (.cons (make_returns _ _ "ChrSeeds" _ _ inert (.cons bound .nil)) (.cons bound (.cons bound
            (.cons bound (.cons bound (.cons bound (.cons (Eval.symbol_returns runtime _ state _)
            (.cons (cons_returns _ state _ _ _ _ bound bound) .nil)))))))))))
      | goals environment goals =>
        rcases environment with _ | ⟨binding, bindings⟩ <;>
        (cases goals with
          | nil =>
            state_case (bound)
            exact make_returns _ _ "ChrState" _ _ inert (.cons bound (.cons bound (.cons bound (.cons bound
              (.cons (Eval.symbol_returns runtime _ state _) (.cons bound .nil))))))
          | cons current goals =>
            state_case (bound)
            exact goal_returns _ state _ table _ current goals tail
              ⟨.goals _ (current :: goals) :: tail, store, history, next, .running, seeds⟩ rfl
              (.cons bound (.cons bound (.cons bound (.cons bound (.cons bound (.cons bound (.cons bound
              (.cons bound (.cons (Eval.symbol_returns runtime _ state _) (.cons bound .nil)))))))))))
      | scan active key values remaining =>
        state_case (bound)
        exact scan_returns _ state _ active key values remaining tail
          ⟨.scan active key values remaining :: tail, store, history, next, .running, seeds⟩
          (fun occurrence after listed => taskReady.1 occurrence (by simp [Mettapedia.Languages.CHR.Machine.Task.occurrences, listed]))
          (.cons bound (.cons bound (.cons bound (.cons bound (.cons bound (.cons bound (.cons bound
          (.cons bound (.cons (Eval.symbol_returns runtime _ state _) (.cons bound .nil))))))))))
      | search active key values occurrence after frames =>
        state_case (bound)
        exact search_returns _ state _ active key values occurrence after frames tail
          ⟨.search active key values occurrence after frames :: tail, store, history, next, .running, seeds⟩
          taskReady.2
          (.cons bound (.cons bound (.cons bound (.cons bound (.cons bound (.cons bound (.cons bound
          (.cons bound (.cons bound (.cons bound (.cons (Eval.symbol_returns runtime _ state _)
          (.cons bound .nil))))))))))))

theorem advance_returns (state : State) (table : Table) (headed : TableHeaded table) :
    ∀ (budget : Nat) (machine : MachineState) (caller : Subst) (first second third : Atom), Ready machine →
      Returns caller state first (programAtom table) → Returns caller state second (stateAtom machine) →
      Returns caller state third (integer budget) →
      Returns caller state (apply "gslt:chr-machine:advance" [first, second, third])
        (stateAtom (Mettapedia.Languages.CHR.Machine.advance table budget machine)) := by
  intro budget
  induction budget with
  | zero =>
    intro machine caller first second third ready one two three
    machine_call (.cons one (.cons two (.cons three .nil)))
    apply pure_if_returns _ _ _ _ (decide (integer ((0 : Nat) : Int) = integer 0)) _ _ _
      (equal_returns _ state _ _ _ _ bound (integer_returns runtime _ state 0))
    simp only [Mettapedia.Languages.CHR.Machine.advance]
    exact bound
  | succ smaller ih =>
    intro machine caller first second third ready one two three
    machine_call (.cons one (.cons two (.cons three .nil)))
    apply pure_if_returns _ _ _ _ (decide (integer ((smaller + 1 : Nat) : Int) = integer 0)) _ _ _
      (equal_returns _ state _ _ _ _ bound (integer_returns runtime _ state 0))
    have different : integer ((smaller + 1 : Nat) : Int) ≠ integer 0 := by
      simp only [integer, ne_eq, Atom.grounded.injEq, OSLFCore.GroundedValue.int.injEq]
      omega
    simp only [different, decide_false, Bool.false_eq_true, ↓reduceIte]
    obtain ⟨tasks, store, history, next, status, seeds⟩ := machine
    cases status with
    | failed =>
      state_case (bound)
      simp only [Mettapedia.Languages.CHR.Machine.advance]
      exact bound
    | faulted reason =>
      state_case (bound)
      simp only [Mettapedia.Languages.CHR.Machine.advance]
      exact bound
    | running =>
      cases tasks with
      | nil =>
        state_case (bound)
        simp only [Mettapedia.Languages.CHR.Machine.advance]
        exact bound
      | cons task tail =>
        state_case (bound)
        simp only [Mettapedia.Languages.CHR.Machine.advance]
        apply ih _ _ _ _ _ (Mettapedia.Languages.CHR.Machine.tick_ready table headed _ ready) bound
          (tick_returns _ state _ _ table _ ready bound bound)
        have cast : integer (smaller : Int) = integer (((smaller + 1 : Nat) : Int) - 1) := by
          simp only [integer, Atom.grounded.injEq, OSLFCore.GroundedValue.int.injEq]
          omega
        rw [cast]
        exact integer_sub_returns runtime _ state _ _ _ 1 bound (integer_returns runtime _ state 1)

/-! ## The package port -/

def runAtom (table : Table) (machine : MachineState) : Atom :=
  .expression [.symbol "ChrRun", programAtom table, stateAtom machine]

/-- The port's answer for a machine state: pending while running with tasks,
otherwise the final status, the store and the posted seed identifiers in
posting order. -/
def resultAtom (machine : MachineState) : Atom :=
  let done := fun status => Atom.expression [.symbol "LangPortDoneV1", .expression [.symbol "ChrMachineResult",
    status, storeAtom machine.store, idsAtom machine.seeds.reverse]]
  match machine.status with
  | .running => if machine.tasks.isEmpty then done (.symbol "ChrComplete") else .symbol "LangPortPendingV1"
  | .failed => done (.symbol "ChrFailed")
  | .faulted reason => done (.expression [.symbol "ChrFaulted", faultAtom reason])

theorem begin_returns (caller : Subst) (state : State) (first second : Atom) (table : Table) (seeds : List Head)
    (one : Returns caller state first (programAtom table))
    (two : Returns caller state second (listAtom (seeds.map headAtom))) :
    Returns caller state (apply "gslt:chr-machine:begin" [first, second])
      (runAtom table (Mettapedia.Languages.CHR.Machine.start seeds)) := by
  machine_call (.cons one (.cons two .nil))
  exact make_returns _ _ "ChrRun" _ _ inert (.cons bound (.cons (start_returns _ state _ seeds bound) .nil))

theorem unit_returns (caller : Subst) (state : State) (first second : Atom) (table : Table)
    (headed : TableHeaded table) (machine : MachineState) (ready : Ready machine) (budget : Nat)
    (one : Returns caller state first (runAtom table machine)) (two : Returns caller state second (integer budget)) :
    Returns caller state (apply "gslt:chr-machine:unit" [first, second])
      (runAtom table (Mettapedia.Languages.CHR.Machine.advance table budget machine)) := by
  machine_call (.cons one (.cons two .nil))
  state_case (bound) unfolding [runAtom]
  exact make_returns _ _ "ChrRun" _ _ inert (.cons bound
    (.cons (advance_returns state table headed budget machine _ _ _ _ ready bound bound bound) .nil))

theorem idsAtom_reverse (seeds : List Nat) :
    listAtom ((seeds.map natAtom).reverse ++ []) = idsAtom seeds.reverse := by
  simp [idsAtom, List.map_reverse]

theorem outcome_returns (caller : Subst) (state : State) (code : Atom) (table : Table) (machine : MachineState)
    (one : Returns caller state code (runAtom table machine)) :
    Returns caller state (apply "gslt:chr-machine:outcome" [code]) (resultAtom machine) := by
  machine_call (.cons one .nil)
  obtain ⟨tasks, store, history, next, status, seeds⟩ := machine
  state_case (bound) unfolding [runAtom]
  apply pure_let_returns _ _ _ "posted" _ (idsAtom seeds.reverse) _ _ (by rfl)
    (by
      rw [← idsAtom_reverse]
      exact reverse_returns state _ [] _ _ _ bound (Eval.symbol_returns runtime _ state _))
  simp only [resultAtom, idsAtom, List.map_reverse]
  cases status with
  | running =>
    state_case (bound)
    cases tasks with
    | nil =>
      state_case (bound)
      exact make_returns _ _ "LangPortDoneV1" _ _ inert (.cons (make_returns _ _ "ChrMachineResult" _ _ inert
        (.cons (Eval.symbol_returns runtime _ state _) (.cons bound (.cons bound .nil)))) .nil)
    | cons task rest =>
      state_case (bound)
      exact Eval.symbol_returns runtime _ state _
  | failed =>
    state_case (bound)
    exact make_returns _ _ "LangPortDoneV1" _ _ inert (.cons (make_returns _ _ "ChrMachineResult" _ _ inert
      (.cons (Eval.symbol_returns runtime _ state _) (.cons bound (.cons bound .nil)))) .nil)
  | faulted reason =>
    state_case (bound)
    exact make_returns _ _ "LangPortDoneV1" _ _ inert (.cons (make_returns _ _ "ChrMachineResult" _ _ inert
      (.cons (make_returns _ _ "ChrFaulted" _ _ inert (.cons bound .nil)) (.cons bound (.cons bound .nil)))) .nil)

#print axioms tick_returns
#print axioms advance_returns
#print axioms begin_returns
#print axioms unit_returns
#print axioms outcome_returns

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CHRMachineExecution
