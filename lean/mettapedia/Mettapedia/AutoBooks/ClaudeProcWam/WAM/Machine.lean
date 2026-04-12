/-
# WAM Machine State

The complete WAM machine state includes:
- Code area (CODE): compiled procedures
- Heap (HEAP): term representation
- Stack (STACK): environment and choice point frames
- Trail (TRAIL): bindings to undo on backtrack
- Registers: P, H, S, E, B, CP, TR, HB, etc.

## Registers

- P: program counter (next instruction address)
- H: heap top (next free heap cell)
- S: structure pointer (for get/unify instructions)
- E: current environment frame
- B: current choice point
- CP: continuation pointer (return address)
- TR: trail top
- HB: heap backtrack point

## References

- Aït-Kaci (1991) Chapter 4: Full WAM with environments
- Warren (1983): Original specification
-/

import Mettapedia.AutoBooks.ClaudeProcWam.WAM.Instructions

namespace Mettapedia.AutoBooks.ClaudeProcWam.WAM

/-! ## Stack Structures

The WAM stack contains both environment frames and choice point frames.
-/

/-- Stack address -/
abbrev StackAddr := Nat

/-- Environment frame for procedure calls -/
structure EnvFrame where
  /-- Continuation environment (caller's E) -/
  ce : StackAddr
  /-- Continuation pointer (return address) -/
  cp : CodeAddr
  /-- Permanent variables Y1..Yn -/
  permanentVars : Array HeapCell
  deriving Repr

/-- Choice point frame for backtracking -/
structure ChoicePoint where
  /-- Number of argument registers to save -/
  n : Nat
  /-- Saved argument registers A1..An -/
  args : Array HeapCell
  /-- Previous environment -/
  ce : StackAddr
  /-- Continuation pointer -/
  cp : CodeAddr
  /-- Previous choice point -/
  b : StackAddr
  /-- Next clause to try -/
  bp : CodeAddr
  /-- Trail pointer at choice point creation -/
  tr : Nat
  /-- Heap pointer at choice point creation -/
  h : HeapAddr
  deriving Repr

/-- Stack frame is either environment or choice point -/
inductive StackFrame where
  | env : EnvFrame → StackFrame
  | choice : ChoicePoint → StackFrame
  deriving Repr

/-- The stack is an array of frames -/
structure Stack where
  frames : Array StackFrame
  deriving Repr

/-- Empty stack -/
def Stack.empty : Stack := ⟨#[]⟩

/-- Push a frame onto stack -/
def Stack.push (s : Stack) (f : StackFrame) : Stack :=
  ⟨s.frames.push f⟩

/-- Get frame at address -/
def Stack.get? (s : Stack) (addr : StackAddr) : Option StackFrame :=
  s.frames[addr]?

/-- Current stack top -/
def Stack.top (s : Stack) : StackAddr := s.frames.size

/-! ## Trail

The trail records bindings made since the last choice point.
On backtracking, these bindings are undone.
-/

/-- Trail entry: address of a bound variable -/
abbrev TrailEntry := HeapAddr

/-- The trail is a list of addresses to unbind -/
structure Trail where
  entries : Array TrailEntry
  deriving Repr

/-- Empty trail -/
def Trail.empty : Trail := ⟨#[]⟩

/-- Push an entry onto trail -/
def Trail.push (t : Trail) (addr : TrailEntry) : Trail :=
  ⟨t.entries.push addr⟩

/-- Current trail top -/
def Trail.top (t : Trail) : Nat := t.entries.size

/-- Unwind trail back to given point -/
def Trail.unwindTo (t : Trail) (point : Nat) : List TrailEntry :=
  (t.entries.toList.drop point)

/-- Truncate trail to given point -/
def Trail.truncateTo (t : Trail) (point : Nat) : Trail :=
  ⟨t.entries.toList.take point |>.toArray⟩

/-! ## Machine State

The complete WAM machine state.
-/

/-- Execution status -/
inductive Status where
  | running    -- Normal execution
  | succeeded  -- Query succeeded
  | failed     -- Current branch failed (may backtrack)
  | halted     -- No more alternatives
  deriving DecidableEq, Repr

instance : ToString Status where
  toString
    | .running => "RUNNING"
    | .succeeded => "SUCCESS"
    | .failed => "FAIL"
    | .halted => "HALTED"

/-- Complete WAM machine state -/
structure MachineState where
  /-- Code store -/
  code : CodeStore
  /-- Heap -/
  heap : Heap
  /-- Stack -/
  stack : Stack
  /-- Trail -/
  trail : Trail
  /-- Register file (X/A registers) -/
  regs : RegisterFile
  /-- Current mode (read/write) -/
  mode : Mode
  /-- Program counter -/
  p : CodeAddr
  /-- Current instruction within procedure -/
  pc : Nat
  /-- Heap top pointer -/
  h : HeapAddr
  /-- Structure pointer -/
  s : HeapAddr
  /-- Current environment frame -/
  e : StackAddr
  /-- Current choice point -/
  b : StackAddr
  /-- Continuation pointer -/
  cp : CodeAddr
  /-- Continuation instruction index -/
  cpc : Nat
  /-- Trail top -/
  tr : Nat
  /-- Heap backtrack point -/
  hb : HeapAddr
  /-- Execution status -/
  status : Status
  /-- Failure flag -/
  fail : Bool
  deriving Repr

/-! ## Machine State Operations -/

/-- Initial machine state with given code -/
def MachineState.initial (code : CodeStore) : MachineState := {
  code := code
  heap := Heap.empty
  stack := Stack.empty
  trail := Trail.empty
  regs := RegisterFile.empty
  mode := .write
  p := 0
  pc := 0
  h := 0
  s := 0
  e := 0
  b := 0
  cp := 0
  cpc := 0
  tr := 0
  hb := 0
  status := .running
  fail := false
}

/-- Get current procedure being executed -/
def MachineState.currentProc? (m : MachineState) : Option Procedure :=
  m.code.procs[m.p]?

/-- Get current instruction -/
def MachineState.currentInstr? (m : MachineState) : Option WAMInstr := do
  let proc ← m.currentProc?
  proc.code[m.pc]?

/-- Read X register -/
def MachineState.getXReg (m : MachineState) (r : XReg) : Option HeapCell :=
  m.regs.get? r

/-- Write X register -/
def MachineState.setXReg (m : MachineState) (r : XReg) (c : HeapCell) : MachineState :=
  { m with regs := m.regs.set r c }

/-- Read Y register (from current environment) -/
def MachineState.getYReg (m : MachineState) (r : YReg) : Option HeapCell := do
  let frame ← m.stack.get? m.e
  match frame with
  | .env ef => ef.permanentVars[r.index]?
  | .choice _ => none

/-- Read any variable register -/
def MachineState.getVarReg (m : MachineState) (r : VarReg) : Option HeapCell :=
  match r with
  | .x xr => m.getXReg xr
  | .y yr => m.getYReg yr

/-- Read from heap -/
def MachineState.getHeap (m : MachineState) (addr : HeapAddr) : Option HeapCell :=
  m.heap.get? addr

/-- Dereference an address -/
def MachineState.deref (m : MachineState) (addr : HeapAddr) : HeapAddr :=
  m.heap.deref addr

/-- Check if address is unbound -/
def MachineState.isUnbound (m : MachineState) (addr : HeapAddr) : Bool :=
  m.heap.isUnbound addr

/-- Push cell onto heap and update H -/
def MachineState.pushHeap (m : MachineState) (c : HeapCell) : MachineState :=
  { m with
    heap := m.heap.push c
    h := m.h + 1 }

/-- Bind address to value and trail if necessary -/
def MachineState.bindAndTrail (m : MachineState) (addr : HeapAddr) (target : HeapAddr) : MachineState :=
  let m' := { m with heap := m.heap.bind addr target }
  -- Trail if addr < HB (older than current choice point)
  if addr < m.hb then
    { m' with trail := m'.trail.push addr, tr := m'.tr + 1 }
  else m'

/-- Set failure flag -/
def MachineState.setFail (m : MachineState) : MachineState :=
  { m with fail := true, status := .failed }

/-- Advance program counter -/
def MachineState.nextInstr (m : MachineState) : MachineState :=
  { m with pc := m.pc + 1 }

/-! ## Backtracking Operations -/

/-- Unwind heap to given address -/
def MachineState.unwindHeapTo (m : MachineState) (addr : HeapAddr) : MachineState :=
  let newCells := m.heap.cells.toList.take addr
  { m with
    heap := ⟨newCells.toArray⟩
    h := addr }

/-- Unwind trail bindings -/
def MachineState.unwindTrailTo (m : MachineState) (point : Nat) : MachineState :=
  let toUnbind := m.trail.unwindTo point
  -- Reset each bound variable to unbound
  let heap' := toUnbind.foldl (fun h addr =>
    h.set addr (.ref addr)) m.heap
  { m with
    heap := heap'
    trail := m.trail.truncateTo point
    tr := point }

/-- Restore state from choice point for backtracking -/
def MachineState.backtrack (m : MachineState) : MachineState :=
  match m.stack.get? m.b with
  | some (.choice cp) =>
    -- Restore argument registers
    let regs' := cp.args.foldl (fun (rf, i) c =>
      (rf.set ⟨i⟩ c, i + 1)) (m.regs, 0) |>.1
    -- Unwind trail
    let m' := m.unwindTrailTo cp.tr
    -- Unwind heap
    let m'' := m'.unwindHeapTo cp.h
    -- Jump to next clause
    { m'' with
      regs := regs'
      e := cp.ce
      cp := cp.cp
      p := 0  -- Would need to resolve cp.bp to procedure index
      pc := 0 -- cp.bp  -- Next clause
      hb := cp.h
      status := .running
      fail := false }
  | _ =>
    -- No choice point, halt
    { m with status := .halted }

/-! ## Pretty Printing -/

instance : ToString MachineState where
  toString m :=
    s!"=== WAM State ===\n" ++
    s!"Status: {m.status}, PC: {m.p}:{m.pc}, Mode: {m.mode}\n" ++
    s!"H: {m.h}, S: {m.s}, E: {m.e}, B: {m.b}, TR: {m.tr}\n" ++
    toString m.heap ++ "\n" ++
    toString m.regs

end Mettapedia.AutoBooks.ClaudeProcWam.WAM
