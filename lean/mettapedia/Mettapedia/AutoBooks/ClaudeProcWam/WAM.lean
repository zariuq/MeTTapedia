/-
# Warren Abstract Machine (WAM) Formalization

A Lean 4 formalization of the Warren Abstract Machine for Prolog.

## Modules

- **Basic**: Foundational types (functors, cells, registers, terms)
- **Heap**: Heap operations (allocation, dereferencing, binding)
- **Instructions**: L0/L1/L2/Full WAM instruction sets
- **Machine**: Complete machine state
- **Unification**: UNION/FIND unification algorithm
- **Semantics**: Small-step operational semantics

## References

Primary sources:
- Warren (1983): An Abstract Prolog Instruction Set (SRI-309)
- Aït-Kaci (1991): WAM: A Tutorial Reconstruction
- Bohrer & Crary (2018): TWAM: A Certifying Abstract Machine

Verification-focused:
- Börger & Rosenzweig (1994): WAM definition and compiler correctness
- Russinoff (1989): Formal verification of the WAM
- Kriener et al. (2013): Prolog semantics equivalences in Coq

## Architecture Overview

```
          ┌─────────────────────────────────────────┐
          │           Source Prolog                 │
          └─────────────────────────────────────────┘
                            │
                            ▼ (Compilation)
          ┌─────────────────────────────────────────┐
          │          WAM Instructions               │
          │  put/get/set/unify/call/proceed/...     │
          └─────────────────────────────────────────┘
                            │
                            ▼ (Execution)
    ┌───────────────────────────────────────────────────────┐
    │                   Machine State                        │
    │  ┌─────────┐  ┌─────────┐  ┌─────────┐  ┌─────────┐   │
    │  │  HEAP   │  │  STACK  │  │  TRAIL  │  │  CODE   │   │
    │  │ (terms) │  │ (envs)  │  │ (undo)  │  │ (procs) │   │
    │  └─────────┘  └─────────┘  └─────────┘  └─────────┘   │
    │  Registers: P, H, S, E, B, CP, TR, HB, A1..An, X1..Xn │
    └───────────────────────────────────────────────────────┘
```

## Formalization Goals

1. **Correctness**: WAM execution corresponds to SLD resolution
2. **Type safety**: Well-typed instructions preserve machine invariants
3. **Termination**: Unification and execution with appropriate measures
4. **Completeness**: Coverage of all WAM instruction effects
-/

import Mettapedia.AutoBooks.ClaudeProcWam.WAM.Basic
import Mettapedia.AutoBooks.ClaudeProcWam.WAM.Heap
import Mettapedia.AutoBooks.ClaudeProcWam.WAM.Instructions
import Mettapedia.AutoBooks.ClaudeProcWam.WAM.Machine
import Mettapedia.AutoBooks.ClaudeProcWam.WAM.Unification
import Mettapedia.AutoBooks.ClaudeProcWam.WAM.Semantics
import Mettapedia.AutoBooks.ClaudeProcWam.WAM.Compiler

namespace Mettapedia.AutoBooks.ClaudeProcWam.WAM

/-! ## Examples -/

/-- Example: Create the functor f/2 -/
example : Functor := mkFunctor "f" 2

/-- Example: Create an empty heap -/
example : Heap := Heap.empty

/-- Example: Push an unbound variable onto heap -/
example : Heap × HeapAddr :=
  Heap.empty.pushUnbound

/-- Example: Create a simple term p(X) -/
example : Term :=
  .app (mkFunctor "p" 1) [.var "X"]

/-- Example: WAM instruction for put_structure h/2, A2 -/
example : WAMInstr :=
  .put_structure (mkFunctor "h" 2) ⟨2⟩

/-- Example: Initialize machine with empty code -/
example : MachineState :=
  MachineState.initial { procs := [] }

end Mettapedia.AutoBooks.ClaudeProcWam.WAM
