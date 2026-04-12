/-
# WAM Instructions

The WAM instruction set is organized by function:
- Put instructions: build query terms
- Get instructions: match program terms
- Set instructions: build subterms (write mode)
- Unify instructions: match subterms (read mode)
- Control instructions: procedure calls, backtracking
- Indexing instructions: first-argument indexing
- Cut instructions: prune search

## Language Levels

- L0: Pure unification (put/set for queries, get/unify for programs)
- L1: Adds argument registers and call/proceed
- L2: Adds backtracking (try/retry/trust, choice points)
- Full WAM: Adds environments, indexing, cut

## References

- Aït-Kaci (1991) Appendix B: WAM instructions summary
- Warren (1983): Original specification
-/

import Mettapedia.AutoBooks.ClaudeProcWam.WAM.Heap

namespace Mettapedia.AutoBooks.ClaudeProcWam.WAM

/-! ## L0 Instructions

L0 handles pure unification without predicates or backtracking.
Query instructions (put/set) build terms on heap.
Program instructions (get/unify) match against heap terms.
-/

/-- L0 Query instructions (build terms) -/
inductive L0QueryInstr where
  /-- Push STR cell + functor, copy to Xi -/
  | put_structure (f : Functor) (xi : XReg)
  /-- Push unbound REF cell, copy to Xi -/
  | set_variable (xi : XReg)
  /-- Push Xi's value onto heap -/
  | set_value (xi : XReg)
  deriving DecidableEq, Repr

/-- L0 Program instructions (match terms) -/
inductive L0ProgInstr where
  /-- Match structure or bind variable -/
  | get_structure (f : Functor) (xi : XReg)
  /-- In read: Xi ← HEAP[S]; in write: push unbound, Xi ← it -/
  | unify_variable (xi : XReg)
  /-- In read: unify Xi with HEAP[S]; in write: push Xi -/
  | unify_value (xi : XReg)
  deriving DecidableEq, Repr

instance : ToString L0QueryInstr where
  toString
    | .put_structure f xi => s!"put_structure {f}, {xi}"
    | .set_variable xi => s!"set_variable {xi}"
    | .set_value xi => s!"set_value {xi}"

instance : ToString L0ProgInstr where
  toString
    | .get_structure f xi => s!"get_structure {f}, {xi}"
    | .unify_variable xi => s!"unify_variable {xi}"
    | .unify_value xi => s!"unify_value {xi}"

/-! ## L1 Instructions

L1 adds argument registers and control flow for multiple facts.
-/

/-- L1 extends L0 with argument register handling -/
inductive L1Instr where
  -- L0 query instructions
  | put_structure (f : Functor) (ai : ArgReg)
  | set_variable (vn : VarReg)
  | set_value (vn : VarReg)
  -- L0 program instructions
  | get_structure (f : Functor) (ai : ArgReg)
  | unify_variable (vn : VarReg)
  | unify_value (vn : VarReg)
  -- Argument handling (new in L1)
  | put_variable (xn : XReg) (ai : ArgReg)  -- First occurrence in query arg position
  | put_value (vn : VarReg) (ai : ArgReg)   -- Later occurrence in query arg position
  | get_variable (vn : VarReg) (ai : ArgReg) -- First occurrence in program arg position
  | get_value (vn : VarReg) (ai : ArgReg)   -- Later occurrence in program arg position
  -- Control (new in L1)
  | call (p : ProcLabel)    -- Call procedure
  | proceed                 -- Return from fact
  deriving DecidableEq, Repr

instance : ToString L1Instr where
  toString
    | .put_structure f ai => s!"put_structure {f}, {ai}"
    | .set_variable vn => s!"set_variable {vn}"
    | .set_value vn => s!"set_value {vn}"
    | .get_structure f ai => s!"get_structure {f}, {ai}"
    | .unify_variable vn => s!"unify_variable {vn}"
    | .unify_value vn => s!"unify_value {vn}"
    | .put_variable xn ai => s!"put_variable {xn}, {ai}"
    | .put_value vn ai => s!"put_value {vn}, {ai}"
    | .get_variable vn ai => s!"get_variable {vn}, {ai}"
    | .get_value vn ai => s!"get_value {vn}, {ai}"
    | .call p => s!"call {p}"
    | .proceed => "proceed"

/-! ## L2 Instructions (Backtracking)

L2 adds choice points and environment frames for backtracking.
-/

/-- Choice instructions for backtracking -/
inductive ChoiceInstr where
  /-- First alternative, else branch to L -/
  | try_me_else (l : CodeLabel)
  /-- Middle alternative, else branch to L -/
  | retry_me_else (l : CodeLabel)
  /-- Last alternative -/
  | trust_me
  /-- Try clause at L (variation) -/
  | try (l : CodeLabel)
  /-- Retry clause at L -/
  | retry (l : CodeLabel)
  /-- Last clause at L -/
  | trust (l : CodeLabel)
  deriving DecidableEq, Repr

/-- Environment instructions -/
inductive EnvInstr where
  /-- Allocate environment frame -/
  | allocate
  /-- Deallocate environment frame -/
  | deallocate
  deriving DecidableEq, Repr

instance : ToString ChoiceInstr where
  toString
    | .try_me_else l => s!"try_me_else {l.offset}"
    | .retry_me_else l => s!"retry_me_else {l.offset}"
    | .trust_me => "trust_me"
    | .try l => s!"try {l.offset}"
    | .retry l => s!"retry {l.offset}"
    | .trust l => s!"trust {l.offset}"

instance : ToString EnvInstr where
  toString
    | .allocate => "allocate"
    | .deallocate => "deallocate"

/-! ## Full WAM Instructions

The complete WAM instruction set.
-/

/-- Indexing instructions for first-argument indexing -/
inductive IndexInstr where
  /-- Switch on first arg type (variable, constant, list, structure) -/
  | switch_on_term (var cons lis str : CodeLabel)
  /-- Hash table for constants -/
  | switch_on_constant (table : List (Functor × CodeLabel))
  /-- Hash table for structures -/
  | switch_on_structure (table : List (Functor × CodeLabel))
  deriving Repr

/-- Cut instructions -/
inductive CutInstr where
  /-- Neck cut: discard choice points -/
  | neck_cut
  /-- Get current choice point level -/
  | get_level (yn : YReg)
  /-- Cut to saved level -/
  | cut (yn : YReg)
  deriving DecidableEq, Repr

instance : ToString CutInstr where
  toString
    | .neck_cut => "neck_cut"
    | .get_level yn => s!"get_level {yn}"
    | .cut yn => s!"cut {yn}"

/-- Full WAM instruction -/
inductive WAMInstr where
  -- Put instructions (query building)
  | put_variable_xn (xn : XReg) (ai : ArgReg)
  | put_variable_yn (yn : YReg) (ai : ArgReg)
  | put_value (vn : VarReg) (ai : ArgReg)
  | put_unsafe_value (yn : YReg) (ai : ArgReg)
  | put_structure (f : Functor) (ai : ArgReg)
  | put_list (ai : ArgReg)
  | put_constant (c : Functor) (ai : ArgReg)
  -- Get instructions (program matching)
  | get_variable (vn : VarReg) (ai : ArgReg)
  | get_value (vn : VarReg) (ai : ArgReg)
  | get_structure (f : Functor) (ai : ArgReg)
  | get_list (ai : ArgReg)
  | get_constant (c : Functor) (ai : ArgReg)
  -- Set instructions (write mode)
  | set_variable (vn : VarReg)
  | set_value (vn : VarReg)
  | set_local_value (vn : VarReg)
  | set_constant (c : Functor)
  | set_void (n : Nat)  -- Push n unbound REFs
  -- Unify instructions (read/write mode)
  | unify_variable (vn : VarReg)
  | unify_value (vn : VarReg)
  | unify_local_value (vn : VarReg)
  | unify_constant (c : Functor)
  | unify_void (n : Nat)
  -- Control instructions
  | allocate
  | deallocate
  | call (p : ProcLabel) (n : Nat)  -- n = number of permanent vars
  | execute (p : ProcLabel)  -- Tail call
  | proceed
  -- Choice instructions
  | try_me_else (l : CodeLabel)
  | retry_me_else (l : CodeLabel)
  | trust_me
  | try (l : CodeLabel)
  | retry (l : CodeLabel)
  | trust (l : CodeLabel)
  -- Indexing instructions
  | switch_on_term (var cons lis str : CodeLabel)
  | switch_on_constant (table : List (Functor × CodeLabel))
  | switch_on_structure (table : List (Functor × CodeLabel))
  -- Cut instructions
  | neck_cut
  | get_level (yn : YReg)
  | cut (yn : YReg)
  deriving Repr

/-! ## Code Representation -/

/-- A basic block is a sequence of instructions -/
abbrev BasicBlock := List WAMInstr

/-- A procedure is a labeled entry point with code -/
structure Procedure where
  label : ProcLabel
  code : BasicBlock
  deriving Repr

/-- Code store maps labels to procedures -/
structure CodeStore where
  procs : List Procedure
  deriving Repr

/-- Lookup a procedure by label -/
def CodeStore.lookup? (cs : CodeStore) (p : ProcLabel) : Option Procedure :=
  cs.procs.find? fun proc => proc.label == p

end Mettapedia.AutoBooks.ClaudeProcWam.WAM
