/-
# WAM Regression Tests

Tests for WAM formalization including:
- Heap operations
- Unification
- Compilation
- Execution
-/

import Mettapedia.AutoBooks.ClaudeProcWam.WAM

namespace Mettapedia.AutoBooks.ClaudeProcWam.WAM.Regression

open WAM

/-! ## Basic Type Tests -/

-- Functors
#check mkFunctor "f" 2  -- f/2
#check mkConstant "a"   -- a/0

-- Heap cells
#check HeapCell.ref 0
#check HeapCell.str 1
#check HeapCell.con (mkConstant "a")

-- Terms
#check Term.var "X"
#check Term.app (mkFunctor "f" 2) [.var "X", .var "Y"]
#check Term.const "a"

/-! ## Heap Operation Tests -/

-- Empty heap
#check Heap.empty
example : Heap.empty.top = 0 := rfl

-- Push unbound variable
example : let (h, addr) := Heap.empty.pushUnbound
          addr = 0 ∧ h.top = 1 := by
  simp [Heap.pushUnbound, Heap.empty, Heap.top, Heap.push]

-- Push structure
example : let (h, addr) := Heap.empty.pushStructure (mkFunctor "f" 2)
          addr = 0 ∧ h.top = 2 := by
  simp [Heap.pushStructure, Heap.empty, Heap.top, Heap.push]

/-! ## Deref Tests -/

-- Self-referential REF is unbound
example : let h : Heap := ⟨#[.ref 0]⟩
          h.deref 0 = 0 := by
  native_decide

-- REF chain dereferencing
example : let h : Heap := ⟨#[.ref 1, .ref 1]⟩
          h.deref 0 = 1 := by
  native_decide

/-! ## Compilation Tests -/

-- Compile variable - verify non-empty output
example : (compileQueryTerm (.var "X")).length > 0 := by
  native_decide

-- Compile constant - verify non-empty output
example : (compileQueryTerm (Term.const "a")).length > 0 := by
  native_decide

-- Compile simple structure f(X)
example : let code := compileQueryTerm (.app (mkFunctor "f" 1) [.var "X"])
          code.length > 0 := by
  native_decide

/-! ## Instruction Tests -/

-- Instruction encoding
#check WAMInstr.put_structure (mkFunctor "f" 2) ⟨1⟩
#check WAMInstr.get_structure (mkFunctor "f" 2) ⟨1⟩
#check WAMInstr.unify_variable (.x ⟨2⟩)
#check WAMInstr.unify_value (.x ⟨2⟩)
#check WAMInstr.call ⟨"p", 2⟩ 0
#check WAMInstr.proceed

/-! ## Machine State Tests -/

-- Initial machine state
example : let m := MachineState.initial { procs := [] }
          m.status = .running := by rfl

-- Check register access
example : let m := MachineState.initial { procs := [] }
          (m.getXReg ⟨0⟩).isSome = true := by
  native_decide

/-! ## Clause Compilation Tests -/

-- Compile a simple fact: p(X).
example : let clause : Clause := {
            head := { pred := ⟨"p", 1⟩, args := [.var "X"] }
            body := []
          }
          let proc := compileClause clause
          proc.label = ⟨"p", 1⟩ := by rfl

-- Compile a fact with structure: p(f(X)).
example : let clause : Clause := {
            head := {
              pred := ⟨"p", 1⟩
              args := [.app (mkFunctor "f" 1) [.var "X"]]
            }
            body := []
          }
          let proc := compileClause clause
          proc.code.length > 0 := by
  native_decide

/-! ## End-to-End Compilation Test -/

/-- Example program: p(a). p(f(X)) :- p(X). -/
def exampleProgram : Program := [
  -- Fact: p(a).
  { head := { pred := ⟨"p", 1⟩, args := [Term.const "a"] }
    body := [] },
  -- Rule: p(f(X)) :- p(X).
  { head := { pred := ⟨"p", 1⟩,
              args := [.app (mkFunctor "f" 1) [.var "X"]] }
    body := [{ pred := ⟨"p", 1⟩, args := [.var "X"] }] }
]

#check compileProgram exampleProgram

-- Verify compilation produces two procedures
example : (compileProgram exampleProgram).procs.length = 2 := by
  native_decide

end Mettapedia.AutoBooks.ClaudeProcWam.WAM.Regression
