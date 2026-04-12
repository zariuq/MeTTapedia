/-
# WAM Operational Semantics

Small-step operational semantics for WAM instructions.

## Instruction Categories

1. Put instructions (query building): Build terms on heap
2. Get instructions (program matching): Match against heap
3. Set instructions (write mode): Build subterms
4. Unify instructions (read/write): Process subterms
5. Control instructions: Call/return/proceed
6. Choice instructions: Backtracking
7. Cut instructions: Pruning

## References

- Aït-Kaci (1991) Appendix B: Instruction definitions
- Börger & Rosenzweig (1994): Formal WAM definition
- Bohrer & Crary (2018): TWAM typing and semantics
-/

import Mettapedia.AutoBooks.ClaudeProcWam.WAM.Unification

namespace Mettapedia.AutoBooks.ClaudeProcWam.WAM

/-! ## Small-Step Semantics

Each instruction transforms the machine state.
-/

/-- Execute put_structure f, Ai -/
def execPutStructure (m : MachineState) (f : Functor) (ai : ArgReg) : MachineState :=
  -- Push functor cell onto heap, then STR pointing to it
  -- Actually WAM: push STR at H, functor at H+1
  let strAddr := m.h
  let m1 := m.pushHeap (.str (strAddr + 1))
  let m2 := m1.pushHeap (.functor f)
  -- Set Ai to the STR cell
  let m3 := m2.setXReg ai (.str strAddr)
  m3.nextInstr

/-- Execute put_list Ai -/
def execPutList (m : MachineState) (ai : ArgReg) : MachineState :=
  -- Set Ai to LIS pointing to current heap top
  let m1 := m.setXReg ai (.lis m.h)
  m1.nextInstr

/-- Execute put_constant c, Ai -/
def execPutConstant (m : MachineState) (c : Functor) (ai : ArgReg) : MachineState :=
  let m1 := m.setXReg ai (.con c)
  m1.nextInstr

/-- Execute put_variable Xn, Ai -/
def execPutVariableX (m : MachineState) (xn : XReg) (ai : ArgReg) : MachineState :=
  -- Push new unbound REF cell
  let addr := m.h
  let m1 := m.pushHeap (.ref addr)
  -- Copy to both Xn and Ai
  let m2 := m1.setXReg xn (.ref addr)
  let m3 := m2.setXReg ai (.ref addr)
  m3.nextInstr

/-- Execute put_variable Yn, Ai -/
def execPutVariableY (m : MachineState) (_yn : YReg) (ai : ArgReg) : MachineState :=
  -- Initialize Yn in current environment to unbound
  -- Set Ai to point to stack location
  -- For simplicity, we push to heap and link
  let addr := m.h
  let m1 := m.pushHeap (.ref addr)
  let m2 := m1.setXReg ai (.ref addr)
  -- TODO: Actually set Yn in environment frame
  m2.nextInstr

/-- Execute put_value Vn, Ai -/
def execPutValue (m : MachineState) (vn : VarReg) (ai : ArgReg) : MachineState :=
  match m.getVarReg vn with
  | some c =>
    let m1 := m.setXReg ai c
    m1.nextInstr
  | none => m.setFail

/-- Execute get_variable Vn, Ai -/
def execGetVariable (m : MachineState) (vn : VarReg) (ai : ArgReg) : MachineState :=
  match m.getXReg ai with
  | some c =>
    match vn with
    | .x xr => (m.setXReg xr c).nextInstr
    -- TODO: handle Y register case
    | .y _ => m.nextInstr
  | none => m.setFail

/-- Execute get_value Vn, Ai -/
def execGetValue (m : MachineState) (vn : VarReg) (ai : ArgReg) : MachineState :=
  match m.getVarReg vn, m.getXReg ai with
  | some (.ref a1), some (.ref a2) =>
    let m1 := m.unify a1 a2
    if m1.fail then m1 else m1.nextInstr
  | _, _ => m.setFail

/-- Execute get_structure f, Ai -/
def execGetStructure (m : MachineState) (f : Functor) (ai : ArgReg) : MachineState :=
  match m.getXReg ai with
  | some cell =>
    let addr := match cell with
      | .ref a => m.deref a
      | .str a => a
      | _ => 0  -- Invalid
    match m.getHeap addr with
    | some (.ref a) =>
      if a == addr then
        -- Unbound variable: bind to new structure, enter write mode
        let strAddr := m.h
        let m1 := m.pushHeap (.str (strAddr + 1))
        let m2 := m1.pushHeap (.functor f)
        let m3 := { m2 with heap := m2.heap.bind addr strAddr }
        { m3 with mode := .write }.nextInstr
      else m.setFail
    | some (.str a) =>
      -- Structure: check functor, enter read mode
      match m.getHeap a with
      | some (.functor f') =>
        if f == f' then
          { m with mode := .read, s := a + 1 }.nextInstr
        else m.setFail
      | _ => m.setFail
    | _ => m.setFail
  | none => m.setFail

/-- Execute get_list Ai -/
def execGetList (m : MachineState) (ai : ArgReg) : MachineState :=
  match m.getXReg ai with
  | some cell =>
    let addr := match cell with
      | .ref a => m.deref a
      | .lis a => a
      | _ => 0
    match m.getHeap addr with
    | some (.ref a) =>
      if a == addr then
        -- Unbound: bind to new list, write mode
        let lisAddr := m.h
        let m1 := { m with heap := m.heap.bind addr lisAddr }
        let m2 := m1.pushHeap (.lis (lisAddr + 1))
        { m2 with mode := .write }.nextInstr
      else m.setFail
    | some (.lis a) =>
      { m with mode := .read, s := a }.nextInstr
    | _ => m.setFail
  | none => m.setFail

/-- Execute get_constant c, Ai -/
def execGetConstant (m : MachineState) (c : Functor) (ai : ArgReg) : MachineState :=
  match m.getXReg ai with
  | some cell =>
    let addr := match cell with
      | .ref a => m.deref a
      | .con _ => 0  -- Handle inline
      | _ => 0
    match cell with
    | .con c' => if c == c' then m.nextInstr else m.setFail
    | .ref _ =>
      match m.getHeap addr with
      | some (.ref a) =>
        if a == addr then
          -- Unbound: bind to constant
          let m1 := { m with heap := m.heap.set addr (.con c) }
          m1.nextInstr
        else m.setFail
      | some (.con c') => if c == c' then m.nextInstr else m.setFail
      | _ => m.setFail
    | _ => m.setFail
  | none => m.setFail

/-- Execute set_variable Vn -/
def execSetVariable (m : MachineState) (vn : VarReg) : MachineState :=
  -- Push new unbound REF, copy to Vn
  let addr := m.h
  let m1 := m.pushHeap (.ref addr)
  match vn with
  | .x xr => (m1.setXReg xr (.ref addr)).nextInstr
  | .y _ => m1.nextInstr  -- TODO: handle Y register

/-- Execute set_value Vn -/
def execSetValue (m : MachineState) (vn : VarReg) : MachineState :=
  match m.getVarReg vn with
  | some c =>
    let m1 := m.pushHeap c
    m1.nextInstr
  | none => m.setFail

/-- Execute set_constant c -/
def execSetConstant (m : MachineState) (c : Functor) : MachineState :=
  let m1 := m.pushHeap (.con c)
  m1.nextInstr

/-- Execute set_void n -/
def execSetVoid (m : MachineState) (n : Nat) : MachineState :=
  let rec pushVoid (m : MachineState) (k : Nat) : MachineState :=
    match k with
    | 0 => m
    | k' + 1 =>
      let addr := m.h
      pushVoid (m.pushHeap (.ref addr)) k'
  (pushVoid m n).nextInstr

/-- Execute unify_variable Vn -/
def execUnifyVariable (m : MachineState) (vn : VarReg) : MachineState :=
  match m.mode with
  | .read =>
    -- Read mode: Vn ← HEAP[S]
    match m.getHeap m.s with
    | some c =>
      let m1 := match vn with
        | .x xr => m.setXReg xr c
        | .y _ => m  -- TODO
      { m1 with s := m1.s + 1 }.nextInstr
    | none => m.setFail
  | .write =>
    -- Write mode: push new unbound REF, copy to Vn
    let addr := m.h
    let m1 := m.pushHeap (.ref addr)
    let m2 := match vn with
      | .x xr => m1.setXReg xr (.ref addr)
      | .y _ => m1
    { m2 with s := m2.s + 1 }.nextInstr

/-- Execute unify_value Vn -/
def execUnifyValue (m : MachineState) (vn : VarReg) : MachineState :=
  match m.mode with
  | .read =>
    -- Read mode: unify Vn with HEAP[S]
    match m.getVarReg vn with
    | some (.ref a) =>
      let m1 := m.unify a m.s
      if m1.fail then m1 else { m1 with s := m1.s + 1 }.nextInstr
    | _ => m.setFail
  | .write =>
    -- Write mode: push Vn's value
    match m.getVarReg vn with
    | some c =>
      let m1 := m.pushHeap c
      { m1 with s := m1.s + 1 }.nextInstr
    | none => m.setFail

/-- Execute unify_constant c -/
def execUnifyConstant (m : MachineState) (c : Functor) : MachineState :=
  match m.mode with
  | .read =>
    let addr := m.deref m.s
    match m.getHeap addr with
    | some (.ref a) =>
      if a == addr then
        -- Unbound: bind to constant
        let m1 := { m with heap := m.heap.set addr (.con c) }
        { m1 with s := m1.s + 1 }.nextInstr
      else m.setFail
    | some (.con c') =>
      if c == c' then { m with s := m.s + 1 }.nextInstr
      else m.setFail
    | _ => m.setFail
  | .write =>
    let m1 := m.pushHeap (.con c)
    { m1 with s := m1.s + 1 }.nextInstr

/-- Execute unify_void n -/
def execUnifyVoid (m : MachineState) (n : Nat) : MachineState :=
  match m.mode with
  | .read =>
    -- Skip n subterms
    { m with s := m.s + n }.nextInstr
  | .write =>
    -- Push n unbound REFs
    (execSetVoid m n)

/-- Execute proceed -/
def execProceed (m : MachineState) : MachineState :=
  -- Return to continuation point
  { m with
    p := m.cp
    pc := m.cpc
    status := if m.cp == 0 && m.cpc == 0 then .succeeded else .running }

/-- Execute call P, N -/
def execCall (m : MachineState) (p : ProcLabel) (_n : Nat) : MachineState :=
  -- Save return address, jump to procedure
  match m.code.procs.findIdx? (fun proc => proc.label == p) with
  | some idx =>
    { m with
      cp := m.p
      cpc := m.pc + 1
      p := idx
      pc := 0 }
  | none => m.setFail

/-- Execute execute P (tail call) -/
def execExecute (m : MachineState) (p : ProcLabel) : MachineState :=
  -- Jump to procedure without saving return address
  match m.code.procs.findIdx? (fun proc => proc.label == p) with
  | some idx => { m with p := idx, pc := 0 }
  | none => m.setFail

/-- Execute allocate -/
def execAllocate (m : MachineState) : MachineState :=
  -- Push environment frame
  let frame : EnvFrame := {
    ce := m.e
    cp := m.cp
    permanentVars := #[]
  }
  let m1 := { m with
    stack := m.stack.push (.env frame)
    e := m.stack.top }
  m1.nextInstr

/-- Execute deallocate -/
def execDeallocate (m : MachineState) : MachineState :=
  -- Pop environment frame
  match m.stack.get? m.e with
  | some (.env ef) =>
    { m with
      cp := ef.cp
      e := ef.ce }.nextInstr
  | _ => m.setFail

/-! ## Main Step Function -/

/-- Single step of WAM execution -/
def MachineState.step (m : MachineState) : MachineState :=
  if m.status != .running then m
  else if m.fail then m.backtrack
  else match m.currentInstr? with
  | none =>
    -- End of procedure
    if m.cp == 0 && m.cpc == 0 then { m with status := .succeeded }
    else { m with p := m.cp, pc := m.cpc }
  | some instr =>
    match instr with
    | .put_structure f ai => execPutStructure m f ai
    | .put_list ai => execPutList m ai
    | .put_constant c ai => execPutConstant m c ai
    | .put_variable_xn xn ai => execPutVariableX m xn ai
    | .put_variable_yn yn ai => execPutVariableY m yn ai
    | .put_value vn ai => execPutValue m vn ai
    | .put_unsafe_value yn ai => execPutValue m (.y yn) ai  -- Simplified
    | .get_variable vn ai => execGetVariable m vn ai
    | .get_value vn ai => execGetValue m vn ai
    | .get_structure f ai => execGetStructure m f ai
    | .get_list ai => execGetList m ai
    | .get_constant c ai => execGetConstant m c ai
    | .set_variable vn => execSetVariable m vn
    | .set_value vn => execSetValue m vn
    | .set_local_value vn => execSetValue m vn  -- Simplified
    | .set_constant c => execSetConstant m c
    | .set_void n => execSetVoid m n
    | .unify_variable vn => execUnifyVariable m vn
    | .unify_value vn => execUnifyValue m vn
    | .unify_local_value vn => execUnifyValue m vn  -- Simplified
    | .unify_constant c => execUnifyConstant m c
    | .unify_void n => execUnifyVoid m n
    | .allocate => execAllocate m
    | .deallocate => execDeallocate m
    | .call p n => execCall m p n
    | .execute p => execExecute m p
    | .proceed => execProceed m
    | .try_me_else _ => m.nextInstr  -- TODO: choice points
    | .retry_me_else _ => m.nextInstr
    | .trust_me => m.nextInstr
    | .try _ => m.nextInstr
    | .retry _ => m.nextInstr
    | .trust _ => m.nextInstr
    | .switch_on_term _ _ _ _ => m.nextInstr  -- TODO: indexing
    | .switch_on_constant _ => m.nextInstr
    | .switch_on_structure _ => m.nextInstr
    | .neck_cut => m.nextInstr  -- TODO: cut
    | .get_level _ => m.nextInstr
    | .cut _ => m.nextInstr

/-- Run machine until termination with fuel -/
def MachineState.run (m : MachineState) (fuel : Nat) : MachineState :=
  match fuel with
  | 0 => m
  | fuel' + 1 =>
    if m.status != .running then m
    else m.step.run fuel'

/-! ## Semantic Properties -/

/-- A machine state is well-formed -/
def MachineState.wellFormed (m : MachineState) : Prop :=
  m.heap.wellFormed ∧
  m.h = m.heap.top ∧
  m.tr = m.trail.entries.size

/-- MachineState.unify preserves MachineState.wellFormed -/
theorem MachineState.unify_preserves_wf (m : MachineState) (a1 a2 : HeapAddr)
    (hwf : m.wellFormed)
    (ha1 : a1 < m.heap.cells.size) (ha2 : a2 < m.heap.cells.size) :
    (m.unify a1 a2).wellFormed := by
  unfold unify wellFormed at *
  let us := UnifyState.fromMachine m a1 a2
  let us' := us.run (m.heap.cells.size * 2 + 10)
  -- us'.toMachine m has heap = us'.heap, h = m.h, tr = us'.trail.entries.size
  constructor
  · -- us'.heap.wellFormed
    have hus_wf : us.heap.wellFormed := hwf.1
    have hpdl : us.pdlValid := by
      intro a ha
      -- us.pdl = [a1, a2] from fromMachine
      have hpdl_eq : us.pdl = [a1, a2] := rfl
      rw [hpdl_eq] at ha
      cases ha with
      | head => exact ha1
      | tail _ htail =>
        cases htail with
        | head => exact ha2
        | tail _ h => nomatch h
    exact UnifyState.run_preserves_wf us _ hus_wf hpdl
  constructor
  · -- m.h = us'.heap.top
    have : us.heap.cells.size = m.heap.cells.size := rfl
    have hrun : us'.heap.cells.size = us.heap.cells.size :=
      UnifyState.run_preserves_heap_size us _
    simp only [UnifyState.toMachine, Heap.top]
    rw [hrun, this, ← Heap.top, ← hwf.2.1]
  · -- tr = trail.entries.size
    simp only [UnifyState.toMachine]

/-- pushVoid helper preserves wellFormed -/
theorem execSetVoid.pushVoid_preserves_wf (m : MachineState) (k : Nat) (hwf : m.wellFormed) :
    (execSetVoid.pushVoid m k).wellFormed := by
  induction k generalizing m with
  | zero => exact hwf
  | succ k' ih =>
    simp only [execSetVoid.pushVoid]
    -- After pushHeap (.ref m.h), we get a new machine state
    unfold MachineState.pushHeap MachineState.wellFormed at *
    have hh_eq : m.h = m.heap.cells.size := hwf.2.1
    apply ih
    constructor
    · -- heap.wellFormed preserved
      rw [hh_eq]
      exact Heap.push_selfref_preserves_wf m.heap hwf.1
    constructor
    · -- h + 1 = (heap.push).top
      rw [Heap.push_top]
      exact congrArg (· + 1) hwf.2.1
    · -- tr unchanged
      exact hwf.2.2

/-- execGetConstant preserves well-formedness.
    All branches either don't modify heap or use set_con_preserves_wf.
    Note: The ref case has complex nested matching that's difficult to reduce. -/
theorem execGetConstant_preserves_wf (m : MachineState) (c : Functor) (ai : ArgReg)
    (hwf : m.wellFormed) : (execGetConstant m c ai).wellFormed := by
  unfold execGetConstant
  cases hget : m.getXReg ai with
  | none => exact hwf
  | some cell =>
    cases cell with
    | con c' =>
      by_cases heq : c == c'
      · simp only [heq, ↓reduceIte]
        unfold MachineState.nextInstr MachineState.wellFormed at *
        exact ⟨hwf.1, hwf.2.1, hwf.2.2⟩
      · simp only [heq, Bool.false_eq_true, ↓reduceIte]
        unfold MachineState.setFail MachineState.wellFormed at *
        exact ⟨hwf.1, hwf.2.1, hwf.2.2⟩
    | ref a =>
      -- Nested match on m.getHeap (m.deref a)
      simp only
      cases hh : m.getHeap (m.deref a) with
      | none =>
        unfold MachineState.setFail MachineState.wellFormed at *
        exact ⟨hwf.1, hwf.2.1, hwf.2.2⟩
      | some hcell =>
        cases hcell with
        | ref a' =>
          by_cases heq : a' == m.deref a
          · -- Unbound: bind to constant
            simp only [heq, ↓reduceIte]
            unfold MachineState.nextInstr MachineState.wellFormed at *
            constructor
            · exact Heap.set_con_preserves_wf m.heap (m.deref a) hwf.1 c
            constructor
            · rw [Heap.set_top]; exact hwf.2.1
            · exact hwf.2.2
          · -- Bound: fail
            simp only [heq, Bool.false_eq_true, ↓reduceIte]
            unfold MachineState.setFail MachineState.wellFormed at *
            exact ⟨hwf.1, hwf.2.1, hwf.2.2⟩
        | con c' =>
          by_cases heq : c == c'
          · simp only [heq, ↓reduceIte]
            unfold MachineState.nextInstr MachineState.wellFormed at *
            exact ⟨hwf.1, hwf.2.1, hwf.2.2⟩
          · simp only [heq, Bool.false_eq_true, ↓reduceIte]
            unfold MachineState.setFail MachineState.wellFormed at *
            exact ⟨hwf.1, hwf.2.1, hwf.2.2⟩
        | str _ =>
          unfold MachineState.setFail MachineState.wellFormed at *
          exact ⟨hwf.1, hwf.2.1, hwf.2.2⟩
        | functor _ =>
          unfold MachineState.setFail MachineState.wellFormed at *
          exact ⟨hwf.1, hwf.2.1, hwf.2.2⟩
        | lis _ =>
          unfold MachineState.setFail MachineState.wellFormed at *
          exact ⟨hwf.1, hwf.2.1, hwf.2.2⟩
    | str _ =>
      unfold MachineState.setFail MachineState.wellFormed at *
      exact ⟨hwf.1, hwf.2.1, hwf.2.2⟩
    | functor _ =>
      unfold MachineState.setFail MachineState.wellFormed at *
      exact ⟨hwf.1, hwf.2.1, hwf.2.2⟩
    | lis _ =>
      unfold MachineState.setFail MachineState.wellFormed at *
      exact ⟨hwf.1, hwf.2.1, hwf.2.2⟩

/-- execGetStructure preserves well-formedness.
    Note: The unbound ref case (push STR + push functor + bind) temporarily
    violates wellFormed during construction. -/
theorem execGetStructure_preserves_wf (m : MachineState) (f : Functor) (ai : ArgReg)
    (hwf : m.wellFormed) : (execGetStructure m f ai).wellFormed := by
  unfold execGetStructure
  cases hget : m.getXReg ai with
  | none =>
    unfold MachineState.setFail MachineState.wellFormed at *
    exact ⟨hwf.1, hwf.2.1, hwf.2.2⟩
  | some cell =>
    simp only
    set addr := match cell with
      | .ref a => m.deref a
      | .str a => a
      | _ => 0 with haddr
    cases hh : m.getHeap addr with
    | none =>
      unfold MachineState.setFail MachineState.wellFormed at *
      exact ⟨hwf.1, hwf.2.1, hwf.2.2⟩
    | some hcell =>
      cases hcell with
      | ref a =>
        by_cases heq : a == addr
        · -- Unbound: push STR + push functor + bind (construction phase)
          simp only [heq, ↓reduceIte]
          sorry
        · -- Bound: fail
          simp only [heq, Bool.false_eq_true, ↓reduceIte]
          unfold MachineState.setFail MachineState.wellFormed at *
          exact ⟨hwf.1, hwf.2.1, hwf.2.2⟩
      | str a =>
        -- Read mode: check functor match
        simp only
        cases hf : m.getHeap a with
        | none =>
          unfold MachineState.setFail MachineState.wellFormed at *
          exact ⟨hwf.1, hwf.2.1, hwf.2.2⟩
        | some fcell =>
          cases fcell with
          | functor f' =>
            by_cases heq : f == f'
            · simp only [heq, ↓reduceIte]
              unfold MachineState.nextInstr MachineState.wellFormed at *
              exact ⟨hwf.1, hwf.2.1, hwf.2.2⟩
            · simp only [heq, Bool.false_eq_true, ↓reduceIte]
              unfold MachineState.setFail MachineState.wellFormed at *
              exact ⟨hwf.1, hwf.2.1, hwf.2.2⟩
          | ref _ =>
            unfold MachineState.setFail MachineState.wellFormed at *
            exact ⟨hwf.1, hwf.2.1, hwf.2.2⟩
          | str _ =>
            unfold MachineState.setFail MachineState.wellFormed at *
            exact ⟨hwf.1, hwf.2.1, hwf.2.2⟩
          | con _ =>
            unfold MachineState.setFail MachineState.wellFormed at *
            exact ⟨hwf.1, hwf.2.1, hwf.2.2⟩
          | lis _ =>
            unfold MachineState.setFail MachineState.wellFormed at *
            exact ⟨hwf.1, hwf.2.1, hwf.2.2⟩
      | con _ =>
        unfold MachineState.setFail MachineState.wellFormed at *
        exact ⟨hwf.1, hwf.2.1, hwf.2.2⟩
      | functor _ =>
        unfold MachineState.setFail MachineState.wellFormed at *
        exact ⟨hwf.1, hwf.2.1, hwf.2.2⟩
      | lis _ =>
        unfold MachineState.setFail MachineState.wellFormed at *
        exact ⟨hwf.1, hwf.2.1, hwf.2.2⟩

/-- execGetList preserves well-formedness.
    Note: The unbound ref case (bind + push) temporarily violates wellFormed
    during construction. A refined invariant distinguishing construction phase
    from execution phase would be needed for a complete proof. -/
theorem execGetList_preserves_wf (m : MachineState) (ai : ArgReg)
    (hwf : m.wellFormed) : (execGetList m ai).wellFormed := by
  unfold execGetList
  cases hget : m.getXReg ai with
  | none =>
    unfold MachineState.setFail MachineState.wellFormed at *
    exact ⟨hwf.1, hwf.2.1, hwf.2.2⟩
  | some cell =>
    simp only
    -- addr is computed from the cell
    set addr := match cell with
      | .ref a => m.deref a
      | .lis a => a
      | _ => 0 with haddr
    cases hh : m.getHeap addr with
    | none =>
      unfold MachineState.setFail MachineState.wellFormed at *
      exact ⟨hwf.1, hwf.2.1, hwf.2.2⟩
    | some hcell =>
      cases hcell with
      | ref a =>
        by_cases heq : a == addr
        · -- Unbound: bind + push (construction phase - needs refined invariant)
          simp only [heq, ↓reduceIte]
          -- This case creates a forward reference that becomes valid after push
          -- but intermediate state violates current wellFormed
          sorry
        · -- Bound: fail
          simp only [heq, Bool.false_eq_true, ↓reduceIte]
          unfold MachineState.setFail MachineState.wellFormed at *
          exact ⟨hwf.1, hwf.2.1, hwf.2.2⟩
      | lis a =>
        -- Read mode: just change mode and s, no heap modification
        simp only
        unfold MachineState.nextInstr MachineState.wellFormed at *
        exact ⟨hwf.1, hwf.2.1, hwf.2.2⟩
      | str _ =>
        unfold MachineState.setFail MachineState.wellFormed at *
        exact ⟨hwf.1, hwf.2.1, hwf.2.2⟩
      | con _ =>
        unfold MachineState.setFail MachineState.wellFormed at *
        exact ⟨hwf.1, hwf.2.1, hwf.2.2⟩
      | functor _ =>
        unfold MachineState.setFail MachineState.wellFormed at *
        exact ⟨hwf.1, hwf.2.1, hwf.2.2⟩

/-- Step preserves well-formedness -/
theorem MachineState.step_preserves_wf (m : MachineState) (hwf : m.wellFormed) :
    m.step.wellFormed := by
  unfold step
  -- Case: status != running
  by_cases hstat : m.status != .running
  · simp only [hstat, ↓reduceIte]
    exact hwf
  · simp only [hstat, Bool.false_eq_true, ↓reduceIte]
    -- Case: fail = true
    by_cases hfail : m.fail
    · simp only [hfail, ↓reduceIte]
      -- backtrack preserves wellFormed
      unfold MachineState.backtrack
      cases hcp : m.stack.get? m.b with
      | none =>
        -- No choice point: just update status to halted
        simp only
        unfold wellFormed at *
        exact ⟨hwf.1, hwf.2.1, hwf.2.2⟩
      | some frame =>
        cases frame with
        | env ef =>
          -- Not a choice point: should also halt (but this branch handles it)
          simp only
          unfold wellFormed at *
          exact ⟨hwf.1, hwf.2.1, hwf.2.2⟩
        | choice cp =>
          -- BLOCKED: Backtrack requires a global invariant about choice point validity.
          -- Key insight: conditional trailing ensures:
          -- (1) At CP creation, heap[0..cp.h) was wellFormed w.r.t. size cp.h
          -- (2) Bindings to cells < cp.h are trailed (conditional trailing with HB = cp.h)
          -- After unwindTrailTo: trailed cells become self-refs (always valid)
          -- After unwindHeapTo: truncate to cp.h, all refs now < cp.h
          -- Resolution: Extend wellFormed to track choice point validity,
          -- specifically: ∀ cp ∈ stack, cp.h was a valid checkpoint and
          -- all bindings to cells < cp.h since creation were trailed.
          simp only
          sorry
    · simp only [hfail, Bool.false_eq_true, ↓reduceIte]
      -- Case: no current instruction
      cases hinstr : m.currentInstr? with
      | none =>
        -- End of procedure: just update status or return address
        unfold wellFormed
        by_cases hcp : m.cp == 0 && m.cpc == 0
        · simp only [hcp, ↓reduceIte]
          exact ⟨hwf.1, hwf.2.1, hwf.2.2⟩
        · simp only [hcp, Bool.false_eq_true, ↓reduceIte]
          exact ⟨hwf.1, hwf.2.1, hwf.2.2⟩
      | some instr =>
        -- Each instruction case
        cases instr with
        | put_structure f ai =>
          -- BLOCKED: put_structure creates STR+functor before subterms are pushed.
          -- Current wellFormed requires a + f.arity < heap.size for STR at a.
          -- For arity > 0, the heap is temporarily "malformed" until set_* pushes subterms.
          -- Resolution: Track "construction phase" or weaken wellFormed for incomplete STRs.
          -- See Heap.push_structure_preserves_wf which handles only arity = 0.
          sorry
        | put_list ai =>
          -- Only modifies regs and pc (sets Ai to LIS pointing to h)
          unfold execPutList setXReg nextInstr wellFormed at *
          simp only [hwf.1, hwf.2.1, hwf.2.2, and_self]
        | put_constant c ai =>
          -- Only modifies regs and pc
          unfold execPutConstant setXReg nextInstr wellFormed at *
          simp only [hwf.1, hwf.2.1, hwf.2.2, and_self]
        | put_variable_xn xn ai =>
          -- Pushes self-ref REF, sets two registers, then nextInstr
          unfold execPutVariableX pushHeap setXReg nextInstr wellFormed at *
          have hh_eq : m.h = m.heap.cells.size := hwf.2.1
          constructor
          · rw [hh_eq]
            exact Heap.push_selfref_preserves_wf m.heap hwf.1
          constructor
          · rw [Heap.push_top]
            exact congrArg (· + 1) hwf.2.1
          · exact hwf.2.2
        | put_variable_yn yn ai =>
          -- Similar to put_variable_xn
          unfold execPutVariableY pushHeap setXReg nextInstr wellFormed at *
          have hh_eq : m.h = m.heap.cells.size := hwf.2.1
          constructor
          · rw [hh_eq]
            exact Heap.push_selfref_preserves_wf m.heap hwf.1
          constructor
          · rw [Heap.push_top]
            exact congrArg (· + 1) hwf.2.1
          · exact hwf.2.2
        | put_value vn ai =>
          -- Only modifies regs and pc (or fails)
          unfold execPutValue wellFormed at *
          cases hget : m.getVarReg vn with
          | none =>
            simp only [hget]
            unfold setFail
            simp only [hwf.1, hwf.2.1, hwf.2.2, and_self]
          | some c =>
            simp only [hget]
            unfold setXReg nextInstr
            simp only [hwf.1, hwf.2.1, hwf.2.2, and_self]
        | put_unsafe_value yn ai =>
          -- Same as put_value (simplified implementation)
          unfold execPutValue wellFormed at *
          cases hget : m.getVarReg (.y yn) with
          | none =>
            simp only [hget]
            unfold setFail
            simp only [hwf.1, hwf.2.1, hwf.2.2, and_self]
          | some c =>
            simp only [hget]
            unfold setXReg nextInstr
            simp only [hwf.1, hwf.2.1, hwf.2.2, and_self]
        | get_variable vn ai =>
          -- Only modifies regs and pc (or fails)
          unfold execGetVariable wellFormed at *
          cases hget : m.getXReg ai with
          | none =>
            simp only [hget]
            unfold setFail
            simp only [hwf.1, hwf.2.1, hwf.2.2, and_self]
          | some c =>
            simp only [hget]
            cases vn with
            | x xr =>
              unfold setXReg nextInstr
              simp only [hwf.1, hwf.2.1, hwf.2.2, and_self]
            | y yr =>
              unfold nextInstr
              simp only [hwf.1, hwf.2.1, hwf.2.2, and_self]
        | get_value vn ai =>
          -- BLOCKED: Requires register validity (addresses in vn, ai < heap.size).
          -- unify_preserves_wf exists but needs preconditions: a1 < size ∧ a2 < size.
          -- Current wellFormed doesn't track register validity.
          -- Resolution: Extend wellFormed to include register validity, or add precondition.
          unfold execGetValue at *
          cases hget1 : m.getVarReg vn with
          | none =>
            simp only [hget1]
            unfold MachineState.setFail MachineState.wellFormed at *
            exact ⟨hwf.1, hwf.2.1, hwf.2.2⟩
          | some c1 =>
            cases hget2 : m.getXReg ai with
            | none =>
              simp only [hget1, hget2]
              unfold MachineState.setFail MachineState.wellFormed at *
              exact ⟨hwf.1, hwf.2.1, hwf.2.2⟩
            | some c2 =>
              simp only [hget1, hget2]
              cases c1 with
              | ref a1 =>
                cases c2 with
                | ref a2 =>
                  -- BLOCKED: Need a1 < heap.size and a2 < heap.size
                  sorry
                | str _ =>
                  unfold MachineState.setFail MachineState.wellFormed at *
                  exact ⟨hwf.1, hwf.2.1, hwf.2.2⟩
                | con _ =>
                  unfold MachineState.setFail MachineState.wellFormed at *
                  exact ⟨hwf.1, hwf.2.1, hwf.2.2⟩
                | functor _ =>
                  unfold MachineState.setFail MachineState.wellFormed at *
                  exact ⟨hwf.1, hwf.2.1, hwf.2.2⟩
                | lis _ =>
                  unfold MachineState.setFail MachineState.wellFormed at *
                  exact ⟨hwf.1, hwf.2.1, hwf.2.2⟩
              | str _ =>
                unfold MachineState.setFail MachineState.wellFormed at *
                exact ⟨hwf.1, hwf.2.1, hwf.2.2⟩
              | con _ =>
                unfold MachineState.setFail MachineState.wellFormed at *
                exact ⟨hwf.1, hwf.2.1, hwf.2.2⟩
              | functor _ =>
                unfold MachineState.setFail MachineState.wellFormed at *
                exact ⟨hwf.1, hwf.2.1, hwf.2.2⟩
              | lis _ =>
                unfold MachineState.setFail MachineState.wellFormed at *
                exact ⟨hwf.1, hwf.2.1, hwf.2.2⟩
        | get_structure f ai =>
          exact execGetStructure_preserves_wf m f ai hwf
        | get_list ai =>
          exact execGetList_preserves_wf m ai hwf
        | get_constant c ai =>
          exact execGetConstant_preserves_wf m c ai hwf
        | set_variable vn =>
          -- Pushes self-ref REF cell at addr = m.h, sets register, then nextInstr
          unfold execSetVariable pushHeap wellFormed at *
          -- Need to show heap after push is wellFormed
          -- m.h = m.heap.top by hwf, so we're pushing .ref m.heap.cells.size
          have hh_eq : m.h = m.heap.cells.size := hwf.2.1
          cases vn with
          | x xr =>
            unfold setXReg nextInstr
            constructor
            · -- heap.wellFormed preserved: pushing .ref (heap.cells.size)
              rw [hh_eq]
              exact Heap.push_selfref_preserves_wf m.heap hwf.1
            constructor
            · -- h + 1 = (heap.push).top
              rw [Heap.push_top]
              exact congrArg (· + 1) hwf.2.1
            · exact hwf.2.2
          | y _ =>
            unfold nextInstr
            constructor
            · rw [hh_eq]
              exact Heap.push_selfref_preserves_wf m.heap hwf.1
            constructor
            · rw [Heap.push_top]
              exact congrArg (· + 1) hwf.2.1
            · exact hwf.2.2
        | set_value vn =>
          -- BLOCKED: Pushes register value to heap. For REF/STR/LIS cells,
          -- need to verify the address is valid. Current wellFormed doesn't track registers.
          unfold execSetValue at *
          cases hget : m.getVarReg vn with
          | none =>
            simp only [hget]
            unfold MachineState.setFail MachineState.wellFormed at *
            exact ⟨hwf.1, hwf.2.1, hwf.2.2⟩
          | some c =>
            simp only [hget]
            -- BLOCKED: Need to know c contains valid addresses
            sorry
        | set_local_value vn =>
          -- Same as set_value (simplified implementation)
          unfold execSetValue at *
          cases hget : m.getVarReg vn with
          | none =>
            simp only [hget]
            unfold MachineState.setFail MachineState.wellFormed at *
            exact ⟨hwf.1, hwf.2.1, hwf.2.2⟩
          | some c =>
            simp only [hget]
            sorry
        | set_constant c =>
          -- Pushes CON cell then nextInstr
          unfold execSetConstant pushHeap nextInstr wellFormed at *
          constructor
          · -- heap.wellFormed preserved
            exact Heap.push_con_preserves_wf m.heap hwf.1 c
          constructor
          · -- h + 1 = (heap.push).top
            rw [Heap.push_top]
            exact congrArg (· + 1) hwf.2.1
          · -- tr unchanged
            exact hwf.2.2
        | set_void n =>
          -- pushVoid n then nextInstr
          unfold execSetVoid wellFormed at *
          have hpush := execSetVoid.pushVoid_preserves_wf m n hwf
          unfold MachineState.nextInstr wellFormed at *
          exact ⟨hpush.1, hpush.2.1, hpush.2.2⟩
        | unify_variable vn =>
          unfold execUnifyVariable wellFormed at *
          cases m.mode with
          | read =>
            -- Read mode: copy from heap to register, increment S
            cases hget : m.getHeap m.s with
            | none =>
              unfold setFail
              simp only [hwf.1, hwf.2.1, hwf.2.2, and_self]
            | some c =>
              cases vn with
              | x xr =>
                unfold setXReg nextInstr
                simp only [hwf.1, hwf.2.1, hwf.2.2, and_self]
              | y yr =>
                unfold nextInstr
                simp only [hwf.1, hwf.2.1, hwf.2.2, and_self]
          | write =>
            -- Write mode: push self-ref REF, set register
            unfold MachineState.pushHeap nextInstr at *
            have hh_eq : m.h = m.heap.cells.size := hwf.2.1
            cases vn with
            | x xr =>
              unfold setXReg
              constructor
              · rw [hh_eq]; exact Heap.push_selfref_preserves_wf m.heap hwf.1
              constructor
              · rw [Heap.push_top]; exact congrArg (· + 1) hwf.2.1
              · exact hwf.2.2
            | y yr =>
              constructor
              · rw [hh_eq]; exact Heap.push_selfref_preserves_wf m.heap hwf.1
              constructor
              · rw [Heap.push_top]; exact congrArg (· + 1) hwf.2.1
              · exact hwf.2.2
        | unify_value vn =>
          -- BLOCKED: Read mode calls unify (needs valid addresses).
          -- Write mode pushes register value (needs register validity).
          unfold execUnifyValue at *
          cases m.mode with
          | read =>
            cases hget : m.getVarReg vn with
            | none =>
              simp only [hget]
              unfold MachineState.setFail MachineState.wellFormed at *
              exact ⟨hwf.1, hwf.2.1, hwf.2.2⟩
            | some c =>
              simp only [hget]
              cases c with
              | ref a =>
                -- BLOCKED: Need a < heap.size and m.s < heap.size
                sorry
              | str _ =>
                unfold MachineState.setFail MachineState.wellFormed at *
                exact ⟨hwf.1, hwf.2.1, hwf.2.2⟩
              | con _ =>
                unfold MachineState.setFail MachineState.wellFormed at *
                exact ⟨hwf.1, hwf.2.1, hwf.2.2⟩
              | functor _ =>
                unfold MachineState.setFail MachineState.wellFormed at *
                exact ⟨hwf.1, hwf.2.1, hwf.2.2⟩
              | lis _ =>
                unfold MachineState.setFail MachineState.wellFormed at *
                exact ⟨hwf.1, hwf.2.1, hwf.2.2⟩
          | write =>
            cases hget : m.getVarReg vn with
            | none =>
              simp only [hget]
              unfold MachineState.setFail MachineState.wellFormed at *
              exact ⟨hwf.1, hwf.2.1, hwf.2.2⟩
            | some c =>
              simp only [hget]
              -- BLOCKED: Need to know c contains valid addresses
              sorry
        | unify_local_value vn =>
          -- Same as unify_value (simplified implementation)
          unfold execUnifyValue at *
          cases m.mode with
          | read =>
            cases hget : m.getVarReg vn with
            | none =>
              simp only [hget]
              unfold MachineState.setFail MachineState.wellFormed at *
              exact ⟨hwf.1, hwf.2.1, hwf.2.2⟩
            | some c =>
              simp only [hget]
              cases c with
              | ref a => sorry
              | str _ =>
                unfold MachineState.setFail MachineState.wellFormed at *
                exact ⟨hwf.1, hwf.2.1, hwf.2.2⟩
              | con _ =>
                unfold MachineState.setFail MachineState.wellFormed at *
                exact ⟨hwf.1, hwf.2.1, hwf.2.2⟩
              | functor _ =>
                unfold MachineState.setFail MachineState.wellFormed at *
                exact ⟨hwf.1, hwf.2.1, hwf.2.2⟩
              | lis _ =>
                unfold MachineState.setFail MachineState.wellFormed at *
                exact ⟨hwf.1, hwf.2.1, hwf.2.2⟩
          | write =>
            cases hget : m.getVarReg vn with
            | none =>
              simp only [hget]
              unfold MachineState.setFail MachineState.wellFormed at *
              exact ⟨hwf.1, hwf.2.1, hwf.2.2⟩
            | some c =>
              simp only [hget]
              sorry
        | unify_constant c =>
          unfold execUnifyConstant wellFormed at *
          cases m.mode with
          | read =>
            -- Read mode: check/bind at deref(S)
            cases hget : m.getHeap (m.deref m.s) with
            | none =>
              simp only [hget]
              unfold setFail
              simp only [hwf.1, hwf.2.1, hwf.2.2, and_self]
            | some cell =>
              simp only [hget]
              cases cell with
              | ref a =>
                by_cases heq : a == m.deref m.s
                · -- Unbound: set to CON
                  simp only [heq, ↓reduceIte]
                  unfold nextInstr
                  constructor
                  · exact Heap.set_con_preserves_wf m.heap (m.deref m.s) hwf.1 c
                  constructor
                  · rw [Heap.set_top]; exact hwf.2.1
                  · exact hwf.2.2
                · -- Bound: fail
                  simp only [heq, Bool.false_eq_true, ↓reduceIte]
                  unfold setFail
                  simp only [hwf.1, hwf.2.1, hwf.2.2, and_self]
              | con c' =>
                by_cases heq : c == c'
                · -- Match: just advance
                  simp only [heq, ↓reduceIte]
                  unfold nextInstr
                  simp only [hwf.1, hwf.2.1, hwf.2.2, and_self]
                · -- No match: fail
                  simp only [heq, Bool.false_eq_true, ↓reduceIte]
                  unfold setFail
                  simp only [hwf.1, hwf.2.1, hwf.2.2, and_self]
              | str _ =>
                unfold setFail
                simp only [hwf.1, hwf.2.1, hwf.2.2, and_self]
              | functor _ =>
                unfold setFail
                simp only [hwf.1, hwf.2.1, hwf.2.2, and_self]
              | lis _ =>
                unfold setFail
                simp only [hwf.1, hwf.2.1, hwf.2.2, and_self]
          | write =>
            -- Write mode: push CON cell
            unfold MachineState.pushHeap nextInstr at *
            constructor
            · exact Heap.push_con_preserves_wf m.heap hwf.1 c
            constructor
            · rw [Heap.push_top]; exact congrArg (· + 1) hwf.2.1
            · exact hwf.2.2
        | unify_void n =>
          unfold execUnifyVoid wellFormed at *
          cases m.mode with
          | read =>
            -- Only changes s and pc
            unfold nextInstr
            exact ⟨hwf.1, hwf.2.1, hwf.2.2⟩
          | write =>
            -- Write mode: calls execSetVoid which uses pushVoid
            -- execSetVoid = (pushVoid m n).nextInstr
            unfold execSetVoid at *
            have hpush := execSetVoid.pushVoid_preserves_wf m n hwf
            unfold nextInstr at *
            exact ⟨hpush.1, hpush.2.1, hpush.2.2⟩
        | allocate =>
          -- Only modifies stack, e, and pc
          unfold execAllocate nextInstr wellFormed at *
          simp only [hwf.1, hwf.2.1, hwf.2.2, and_self]
        | deallocate =>
          -- Only modifies cp, e, pc (or fails)
          unfold execDeallocate wellFormed at *
          cases hget : m.stack.get? m.e with
          | none =>
            unfold setFail
            simp only [hwf.1, hwf.2.1, hwf.2.2, and_self]
          | some frame =>
            cases frame with
            | env ef =>
              unfold nextInstr
              simp only [hwf.1, hwf.2.1, hwf.2.2, and_self]
            | choice cp =>
              unfold setFail
              simp only [hwf.1, hwf.2.1, hwf.2.2, and_self]
        | call p n =>
          -- Only modifies cp, cpc, p, pc (or fails)
          unfold execCall wellFormed at *
          cases hfind : m.code.procs.findIdx? (fun proc => proc.label == p) with
          | none =>
            simp only [hfind]
            unfold setFail
            simp only [hwf.1, hwf.2.1, hwf.2.2, and_self]
          | some idx =>
            simp only [hfind, hwf.1, hwf.2.1, hwf.2.2, and_self]
        | execute p =>
          -- Only modifies p, pc (or fails)
          unfold execExecute wellFormed at *
          cases hfind : m.code.procs.findIdx? (fun proc => proc.label == p) with
          | none =>
            simp only [hfind]
            unfold setFail
            simp only [hwf.1, hwf.2.1, hwf.2.2, and_self]
          | some idx =>
            simp only [hfind, hwf.1, hwf.2.1, hwf.2.2, and_self]
        | proceed =>
          -- proceed only changes p, pc, status
          unfold execProceed wellFormed
          simp only [hwf.1, hwf.2.1, hwf.2.2, and_self]
        | try_me_else l =>
          -- Just nextInstr
          unfold MachineState.nextInstr wellFormed at *
          simp only [hwf.1, hwf.2.1, hwf.2.2, and_self]
        | retry_me_else l =>
          unfold MachineState.nextInstr wellFormed at *
          simp only [hwf.1, hwf.2.1, hwf.2.2, and_self]
        | trust_me =>
          unfold MachineState.nextInstr wellFormed at *
          simp only [hwf.1, hwf.2.1, hwf.2.2, and_self]
        | «try» l =>
          unfold MachineState.nextInstr wellFormed at *
          simp only [hwf.1, hwf.2.1, hwf.2.2, and_self]
        | «retry» l =>
          unfold MachineState.nextInstr wellFormed at *
          simp only [hwf.1, hwf.2.1, hwf.2.2, and_self]
        | «trust» l =>
          unfold MachineState.nextInstr wellFormed at *
          simp only [hwf.1, hwf.2.1, hwf.2.2, and_self]
        | switch_on_term a b c d =>
          unfold MachineState.nextInstr wellFormed at *
          simp only [hwf.1, hwf.2.1, hwf.2.2, and_self]
        | switch_on_constant t =>
          unfold MachineState.nextInstr wellFormed at *
          simp only [hwf.1, hwf.2.1, hwf.2.2, and_self]
        | switch_on_structure t =>
          unfold MachineState.nextInstr wellFormed at *
          simp only [hwf.1, hwf.2.1, hwf.2.2, and_self]
        | neck_cut =>
          unfold MachineState.nextInstr wellFormed at *
          simp only [hwf.1, hwf.2.1, hwf.2.2, and_self]
        | get_level yn =>
          unfold MachineState.nextInstr wellFormed at *
          simp only [hwf.1, hwf.2.1, hwf.2.2, and_self]
        | cut yn =>
          unfold MachineState.nextInstr wellFormed at *
          simp only [hwf.1, hwf.2.1, hwf.2.2, and_self]

/-- Successful execution implies unification soundness.
    TODO: Define actual soundness property relating WAM execution to logical unification.
    Current statement is a placeholder - the real theorem would state:
    - If execution succeeds, the heap represents a valid substitution
    - The original query and program terms unify under this substitution -/
theorem MachineState.success_sound (m : MachineState) (fuel : Nat)
    (hsucc : (m.run fuel).status = .succeeded) :
    True := trivial

end Mettapedia.AutoBooks.ClaudeProcWam.WAM
