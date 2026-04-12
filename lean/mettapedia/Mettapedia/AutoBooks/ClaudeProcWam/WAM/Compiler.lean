/-
# WAM Compiler

Compiles Prolog source (terms, atoms, clauses) to WAM instructions.

## Compilation Phases

1. **Register Allocation**: Assign registers to term positions
2. **Term Flattening**: Linearize nested term structure
3. **Code Generation**: Emit WAM instructions

## References

- Aït-Kaci (1991) §2.2-2.4: Query and program compilation
- Warren (1983): Original compilation scheme
-/

import Mettapedia.AutoBooks.ClaudeProcWam.WAM.Instructions

namespace Mettapedia.AutoBooks.ClaudeProcWam.WAM

/-! ## Register Allocation -/

/-- Register allocation state -/
structure RegAlloc where
  /-- Next available register index -/
  nextReg : RegIndex
  /-- Map from variable names to registers -/
  varMap : List (VarName × XReg)
  /-- Registers seen so far (for tracking first occurrence) -/
  seen : List XReg
  deriving Repr, Inhabited

/-- Initial register allocation starting at X1 -/
def RegAlloc.init : RegAlloc := {
  nextReg := 1
  varMap := []
  seen := []
}

/-- Allocate a fresh register -/
def RegAlloc.fresh (ra : RegAlloc) : RegAlloc × XReg :=
  ({ ra with nextReg := ra.nextReg + 1 }, ⟨ra.nextReg⟩)

/-- Look up variable -/
def RegAlloc.lookup (ra : RegAlloc) (v : VarName) : Option XReg :=
  ra.varMap.lookup v

/-- Check if variable was seen before -/
def RegAlloc.wasSeen (ra : RegAlloc) (v : VarName) : Bool :=
  (ra.lookup v).isSome

/-- Register a variable at given register -/
def RegAlloc.bind (ra : RegAlloc) (v : VarName) (r : XReg) : RegAlloc :=
  { ra with varMap := (v, r) :: ra.varMap }

/-- Mark register as seen -/
def RegAlloc.markSeen (ra : RegAlloc) (r : XReg) : RegAlloc :=
  { ra with seen := r :: ra.seen }

/-- Get or allocate register for variable -/
def RegAlloc.getOrAlloc (ra : RegAlloc) (v : VarName) : RegAlloc × XReg × Bool :=
  match ra.lookup v with
  | some r => (ra, r, true)  -- Already seen
  | none =>
    let (ra', r) := ra.fresh
    (ra'.bind v r |>.markSeen r, r, false)

/-! ## Simple Compilation

A simplified compiler that handles basic cases.
For production use, would need full flattening.
-/

/-- Compile instructions for a variable in query position -/
def compileQueryVar (ra : RegAlloc) (v : VarName) (targetReg : XReg)
    : RegAlloc × List WAMInstr :=
  match ra.lookup v with
  | some r =>
    -- Already seen: put_value
    (ra, [.put_value (.x r) targetReg])
  | none =>
    -- First occurrence: put_variable
    let ra' := ra.bind v targetReg |>.markSeen targetReg
    (ra', [.put_variable_xn targetReg targetReg])

/-- Compile instructions for a structure in query position -/
def compileQueryStructure (ra : RegAlloc) (f : Functor) (args : List Term)
    (targetReg : XReg) (fuel : Nat) : RegAlloc × List WAMInstr :=
  match fuel with
  | 0 => (ra, [])  -- Out of fuel
  | fuel' + 1 =>
    -- First, compile subterms and collect their instructions
    let (ra', subInstrs, argRegs) := args.foldl (fun acc arg =>
      let (ra, instrs, regs) := acc
      match arg with
      | .var v =>
        let (ra', r, _) := ra.getOrAlloc v
        (ra', instrs, regs ++ [r])
      | .app f' args' =>
        let (ra', r) := ra.fresh
        let (ra'', subCode) := compileQueryStructure ra' f' args' r fuel'
        (ra'', instrs ++ subCode, regs ++ [r])
    ) (ra, [], [])
    -- Then emit put_structure and set instructions
    let putInstr := WAMInstr.put_structure f targetReg
    let setInstrs := argRegs.map fun r =>
      if ra'.seen.contains r then WAMInstr.set_value (.x r)
      else WAMInstr.set_variable (.x r)
    (ra'.markSeen targetReg, subInstrs ++ [putInstr] ++ setInstrs)

/-- Compile a query term -/
def compileQueryTermAux (ra : RegAlloc) (t : Term) (targetReg : XReg)
    (fuel : Nat) : RegAlloc × List WAMInstr :=
  match t with
  | .var v => compileQueryVar ra v targetReg
  | .app f args => compileQueryStructure ra f args targetReg fuel

/-- Compile a query term with default fuel -/
def compileQueryTerm (t : Term) : List WAMInstr :=
  let (_, instrs) := compileQueryTermAux RegAlloc.init t ⟨1⟩ 100
  instrs

/-- Compile instructions for a variable in program position -/
def compileProgVar (ra : RegAlloc) (v : VarName) (targetReg : XReg)
    : RegAlloc × List WAMInstr :=
  match ra.lookup v with
  | some r =>
    -- Already seen: get_value
    (ra, [.get_value (.x r) targetReg])
  | none =>
    -- First occurrence: get_variable
    let ra' := ra.bind v targetReg |>.markSeen targetReg
    (ra', [.get_variable (.x targetReg) targetReg])

/-- Compile a program term (matching mode) -/
def compileProgTermAux (ra : RegAlloc) (t : Term) (targetReg : XReg)
    (fuel : Nat) : RegAlloc × List WAMInstr :=
  match fuel with
  | 0 => (ra, [])
  | fuel' + 1 =>
    match t with
    | .var v => compileProgVar ra v targetReg
    | .app f args =>
      -- get_structure instruction
      let getInstr := WAMInstr.get_structure f targetReg
      -- Process arguments with unify instructions
      let (ra', unifyInstrs) := args.foldl (fun acc arg =>
        let (ra, instrs) := acc
        match arg with
        | .var v =>
          let (ra', r, wasSeen) := ra.getOrAlloc v
          let instr := if wasSeen then WAMInstr.unify_value (.x r)
                       else WAMInstr.unify_variable (.x r)
          (ra', instrs ++ [instr])
        | .app f' args' =>
          let (ra', r) := ra.fresh
          let unifyVar := WAMInstr.unify_variable (.x r)
          let (ra'', nestedInstrs) := compileProgTermAux ra' (.app f' args') r fuel'
          (ra'', instrs ++ [unifyVar] ++ nestedInstrs)
      ) (ra.markSeen targetReg, [])
      (ra', [getInstr] ++ unifyInstrs)

/-- Compile a program term with default fuel -/
def compileProgTerm (t : Term) (argReg : ArgReg) : List WAMInstr :=
  let (_, instrs) := compileProgTermAux RegAlloc.init t argReg 100
  instrs

/-! ## Atom and Clause Compilation -/

/-- Compile a query atom (goal) -/
def compileQueryAtom (a : Atom) : List WAMInstr :=
  let rec compileArgs (ra : RegAlloc) (args : List Term) (idx : Nat)
      : RegAlloc × List WAMInstr :=
    match args with
    | [] => (ra, [])
    | arg :: rest =>
      let argReg : ArgReg := ⟨idx⟩
      let (ra', argInstrs) := compileQueryTermAux ra arg argReg 100
      let (ra'', restInstrs) := compileArgs ra' rest (idx + 1)
      (ra'', argInstrs ++ restInstrs)
  let (_, argInstrs) := compileArgs RegAlloc.init a.args 1
  let callInstr := WAMInstr.call a.pred 0
  argInstrs ++ [callInstr]

/-- Compile a program atom (clause head) -/
def compileProgAtom (a : Atom) : List WAMInstr :=
  let rec compileArgs (ra : RegAlloc) (args : List Term) (idx : Nat)
      : RegAlloc × List WAMInstr :=
    match args with
    | [] => (ra, [])
    | arg :: rest =>
      let argReg : ArgReg := ⟨idx⟩
      let (ra', argInstrs) := compileProgTermAux ra arg argReg 100
      let (ra'', restInstrs) := compileArgs ra' rest (idx + 1)
      (ra'', argInstrs ++ restInstrs)
  let (_, instrs) := compileArgs RegAlloc.init a.args 1
  instrs

/-- Compile a clause to a procedure -/
def compileClause (c : Clause) : Procedure :=
  let headCode := compileProgAtom c.head
  let bodyCode := c.body.map compileQueryAtom |>.flatten
  let finalInstr := WAMInstr.proceed
  { label := c.head.pred
    code := headCode ++ bodyCode ++ [finalInstr] }

/-- Compile a program to a code store -/
def compileProgram (p : Program) : CodeStore :=
  { procs := p.map compileClause }

/-! ## Examples -/

/-- Example: Compile query p(Z, f(Z)) -/
example : List WAMInstr :=
  let term := Term.app (mkFunctor "p" 2) [
    .var "Z",
    .app (mkFunctor "f" 1) [.var "Z"]
  ]
  compileQueryTerm term

/-- Example: Compile fact p(X, f(X)) -/
example : Procedure :=
  let clause : Clause := {
    head := {
      pred := ⟨"p", 2⟩
      args := [.var "X", .app (mkFunctor "f" 1) [.var "X"]]
    }
    body := []
  }
  compileClause clause

end Mettapedia.AutoBooks.ClaudeProcWam.WAM
