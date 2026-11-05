import Mathlib.Tactic

/-!
# AArch64 Phase-4 scheduler and containment laws

The finite policy behind the Cesta GIC/timer mechanism: one current task,
one saved frame per task, and task-B-only fault containment.  Device-register
programming and exception-frame assembly remain separate native boundaries.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Kernel.Arm64Phase4

inductive Task where
  | a | b
  deriving DecidableEq, Repr

structure State where
  frameA : Nat
  frameB : Nat
  current : Task
  started : Bool
  bDead : Bool
  deriving DecidableEq, Repr

def Valid (state : State) : Prop :=
  state.started = true ∧ state.frameA ≠ 0 ∧ state.frameB ≠ 0 ∧
    state.frameA ≠ state.frameB ∧ (state.bDead = true → state.current = .a)

def PmrReadbackValid (pmr : Nat) : Prop :=
  pmr = 0xf8 ∨ pmr = 0xfc ∨ pmr = 0xfe ∨ pmr = 0xff

theorem pmrReadbackValid_minimum {pmr : Nat} (valid : PmrReadbackValid pmr) :
    0xf8 ≤ pmr ∧ pmr ≤ 0xff := by
  rcases valid with rfl | rfl | rfl | rfl <;> norm_num

def initState (frameA frameB : Nat) : Option State :=
  if frameA = 0 ∨ frameB = 0 ∨ frameA = frameB then none
  else some (State.mk frameA frameB Task.a true false)

def tick (state : State) (frame intid : Nat) : Option (State × Nat) :=
  if state.started = false ∨ frame = 0 ∨ state.frameA = 0 ∨ state.frameB = 0 then none
  else if intid ≠ 30 then none
  else
    let saved := match state.current with
      | .a => { state with frameA := frame }
      | .b => { state with frameB := frame }
    let next := if saved.bDead then .a else match saved.current with | .a => .b | .b => .a
    let result := { saved with current := next }
    some (result, if next = .a then result.frameA else result.frameB)

def containFault (state : State) (frame : Nat) : Option (State × Nat) :=
  if state.frameA = 0 ∨ state.frameB = 0 ∨ frame = 0 then none
  else if state.started = false then none
  else if state.current ≠ .b then none
  else
    let result := { state with frameB := frame, bDead := true, current := .a }
    some (result, result.frameA)

theorem initState_valid {frameA frameB : Nat} {state : State}
    (accepted : initState frameA frameB = some state) : Valid state := by
  unfold initState at accepted
  split at accepted
  · contradiction
  · simp only [Option.some.injEq] at accepted
    subst state
    simp_all [Valid]

theorem tick_wrong_interrupt (state : State) (frame intid : Nat)
    (wrong : intid ≠ 30) : tick state frame intid = none := by
  simp [tick, wrong]

theorem containFault_preserves_a {state next : State} {frame resume : Nat}
    (accepted : containFault state frame = some (next, resume)) :
    next.frameA = state.frameA ∧ resume = state.frameA := by
  unfold containFault at accepted
  split at accepted <;> try contradiction
  split at accepted <;> try contradiction
  split at accepted <;> try contradiction
  simp only [Option.some.injEq, Prod.mk.injEq] at accepted
  rcases accepted with ⟨rfl, rfl⟩
  simp

theorem containFault_retires_b {state next : State} {frame resume : Nat}
    (accepted : containFault state frame = some (next, resume)) :
    next.bDead = true ∧ next.current = .a ∧ next.frameB = frame := by
  unfold containFault at accepted
  split at accepted <;> try contradiction
  split at accepted <;> try contradiction
  split at accepted <;> try contradiction
  simp only [Option.some.injEq, Prod.mk.injEq] at accepted
  rcases accepted with ⟨rfl, rfl⟩
  simp

theorem dead_task_never_resumes {state next : State} {frame resume : Nat}
    (dead : state.bDead = true)
    (accepted : tick state frame 30 = some (next, resume)) :
    next.current = .a ∧ resume = next.frameA := by
  cases current : state.current <;>
    simp [tick, dead, current] at accepted <;>
    rcases accepted with ⟨_, rfl, rfl⟩ <;> simp

namespace Controls

def start : State :=
  State.mk 100 200 Task.a true false

example : tick start 300 29 = none := by rfl

example : tick start 300 30 =
    some (State.mk 300 200 Task.b true false, 200) := by rfl

def taskB : State :=
  State.mk 300 400 Task.b true false

example : containFault taskB 600 =
    some (State.mk 300 600 Task.a true true, 300) := by rfl

example : containFault start 600 = none := by rfl

def deadA : State := State.mk 300 400 Task.a true true

example : tick deadA 700 30 =
    some (State.mk 700 400 Task.a true true, 700) := by rfl

example : PmrReadbackValid 0xf8 := by simp [PmrReadbackValid]
example : PmrReadbackValid 0xff := by simp [PmrReadbackValid]
example : ¬PmrReadbackValid 0xf0 := by norm_num [PmrReadbackValid]
example : ¬PmrReadbackValid 0xf9 := by norm_num [PmrReadbackValid]

end Controls

#print axioms initState_valid
#print axioms pmrReadbackValid_minimum
#print axioms tick_wrong_interrupt
#print axioms containFault_preserves_a
#print axioms containFault_retires_b
#print axioms dead_task_never_resumes

end Mettapedia.Machines.Kernel.Arm64Phase4
