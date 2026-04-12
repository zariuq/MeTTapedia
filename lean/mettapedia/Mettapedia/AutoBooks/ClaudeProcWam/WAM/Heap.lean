/-
# WAM Heap Operations

The WAM heap is a global array of cells used to represent terms.
Key operations:
- Allocation: push cells onto heap
- Dereferencing: follow REF chains to find canonical representative
- Binding: link unbound variables to terms
- Unification: the core UNION/FIND algorithm

## References

- Aït-Kaci (1991) §2.1: Term representation
- Aït-Kaci (1991) §2.3: Dereferencing and binding
- Warren (1983): Original WAM specification
-/

import Mettapedia.AutoBooks.ClaudeProcWam.WAM.Basic

namespace Mettapedia.AutoBooks.ClaudeProcWam.WAM

/-! ## Heap Structure -/

/-- The heap is an array of cells with a high-water mark H -/
structure Heap where
  cells : Array HeapCell
  deriving Repr

/-- Empty heap -/
def Heap.empty : Heap := ⟨#[]⟩

/-- Current heap top (next free address) -/
def Heap.top (h : Heap) : HeapAddr := h.cells.size

/-- Read a cell from the heap (returns none if out of bounds) -/
def Heap.get? (h : Heap) (addr : HeapAddr) : Option HeapCell :=
  h.cells[addr]?

/-- Read a cell, with proof that address is valid -/
def Heap.get (h : Heap) (addr : HeapAddr) (hlt : addr < h.cells.size) : HeapCell :=
  h.cells[addr]

/-- Set a cell in the heap -/
def Heap.set (h : Heap) (addr : HeapAddr) (cell : HeapCell) : Heap :=
  if hlt : addr < h.cells.size then
    ⟨h.cells.set addr cell⟩
  else h

/-- Push a cell onto the heap -/
def Heap.push (h : Heap) (cell : HeapCell) : Heap :=
  ⟨h.cells.push cell⟩

/-- Push multiple cells onto the heap -/
def Heap.pushMany (h : Heap) (cells : List HeapCell) : Heap :=
  ⟨cells.foldl Array.push h.cells⟩

instance : ToString Heap where
  toString h :=
    let cells := h.cells.toList
    let rec go (i : Nat) : List HeapCell → List String
      | [] => []
      | c :: cs => s!"  {i}: {c}" :: go (i + 1) cs
    "HEAP:\n" ++ String.intercalate "\n" (go 0 cells)

/-! ## Dereferencing

Dereferencing follows REF chains until reaching either:
- An unbound REF cell (self-referential)
- A non-REF cell (STR, CON, LIS, or functor)

This is the core of UNION/FIND composition of substitutions.
-/

/-- Check if a cell is an unbound variable (self-referential REF) -/
def HeapCell.isUnbound (c : HeapCell) (addr : HeapAddr) : Bool :=
  match c with
  | .ref a => a == addr
  | _ => false

/-- Dereferencing with fuel (to ensure termination) -/
def Heap.derefAux (h : Heap) (addr : HeapAddr) (fuel : Nat) : HeapAddr :=
  match fuel with
  | 0 => addr  -- Out of fuel, return current
  | fuel' + 1 =>
    match h.get? addr with
    | none => addr  -- Invalid address, return as-is
    | some (.ref a) =>
      if a == addr then addr  -- Unbound variable
      else h.derefAux a fuel'  -- Follow reference
    | some _ => addr  -- Non-REF cell, done

/-- Dereference an address: follow REF chain to canonical form -/
def Heap.deref (h : Heap) (addr : HeapAddr) : HeapAddr :=
  h.derefAux addr h.cells.size

/-- Check if an address points to an unbound variable -/
def Heap.isUnbound (h : Heap) (addr : HeapAddr) : Bool :=
  let d := h.deref addr
  match h.get? d with
  | some c => c.isUnbound d
  | none => false

/-! ## Binding

Binding links an unbound variable to another address.
In the basic WAM, binding direction is arbitrary when both are unbound.
In the full WAM, we prefer binding newer variables to older ones (for trailing).
-/

/-- Bind address a1 to a2 (assuming a1 points to unbound REF) -/
def Heap.bind (h : Heap) (a1 a2 : HeapAddr) : Heap :=
  h.set a1 (.ref a2)

/-- Smart binding: binds the "younger" (higher address) to the "older" -/
def Heap.smartBind (h : Heap) (a1 a2 : HeapAddr) : Heap :=
  if a1 > a2 then h.set a1 (.ref a2)
  else if a2 > a1 then h.set a2 (.ref a1)
  else h  -- Same address, no binding needed

/-! ## Heap Construction Helpers

These help build term representations on the heap.
-/

/-- Push an unbound REF cell (new variable) -/
def Heap.pushUnbound (h : Heap) : Heap × HeapAddr :=
  let addr := h.top
  (h.push (.ref addr), addr)

/-- Push a STR cell pointing to a functor -/
def Heap.pushStructure (h : Heap) (f : Functor) : Heap × HeapAddr :=
  let strAddr := h.top
  let h1 := h.push (.str (strAddr + 1))
  let h2 := h1.push (.functor f)
  (h2, strAddr)

/-- Push a constant cell -/
def Heap.pushConstant (h : Heap) (f : Functor) : Heap × HeapAddr :=
  let addr := h.top
  (h.push (.con f), addr)

/-- Push a LIS cell -/
def Heap.pushList (h : Heap) : Heap × HeapAddr :=
  let addr := h.top
  (h.push (.lis (addr + 1)), addr)

/-! ## Register File -/

/-- Register file maps register indices to heap cells -/
structure RegisterFile where
  regs : Array HeapCell
  deriving Repr

/-- Empty register file with n registers -/
def RegisterFile.empty (n : Nat := 256) : RegisterFile :=
  let rec build (k : Nat) (acc : Array HeapCell) : Array HeapCell :=
    match k with
    | 0 => acc
    | k' + 1 => build k' (acc.push (.ref 0))
  ⟨build n #[]⟩

/-- Get register value -/
def RegisterFile.get? (rf : RegisterFile) (r : XReg) : Option HeapCell :=
  rf.regs[r.index]?

def RegisterFile.get (rf : RegisterFile) (r : XReg) (hlt : r.index < rf.regs.size) : HeapCell :=
  rf.regs[r.index]

/-- Set register value -/
def RegisterFile.set (rf : RegisterFile) (r : XReg) (c : HeapCell) : RegisterFile :=
  if hlt : r.index < rf.regs.size then
    ⟨rf.regs.set r.index c⟩
  else rf

instance : ToString RegisterFile where
  toString rf :=
    let regs := rf.regs.toList
    let rec go (i : Nat) : List HeapCell → List String
      | [] => []
      | c :: cs =>
        match c with
        | .ref 0 => go (i + 1) cs  -- Skip default
        | _ => s!"  X{i}: {c}" :: go (i + 1) cs
    "REGS:\n" ++ String.intercalate "\n" (go 0 regs)

/-! ## Store: Unified Access to Heap and Registers

STORE[a] notation in WAM refers to either heap or registers.
We model this with a sum type for addresses.
-/

/-- A store address can be heap or register -/
inductive StoreAddr where
  | heap : HeapAddr → StoreAddr
  | reg : XReg → StoreAddr
  deriving DecidableEq, Repr

/-- Combined store of heap and registers -/
structure Store where
  heap : Heap
  regs : RegisterFile
  deriving Repr

/-- Read from store -/
def Store.get? (s : Store) : StoreAddr → Option HeapCell
  | .heap a => s.heap.get? a
  | .reg r => s.regs.get? r

/-- Write to store -/
def Store.set (s : Store) (addr : StoreAddr) (c : HeapCell) : Store :=
  match addr with
  | .heap a => { s with heap := s.heap.set a c }
  | .reg r => { s with regs := s.regs.set r c }

/-- Dereference through the store -/
def Store.deref (s : Store) (addr : StoreAddr) : StoreAddr :=
  match addr with
  | .heap a => .heap (s.heap.deref a)
  | .reg r =>
    match s.regs.get? r with
    | some (.ref a) => .heap (s.heap.deref a)
    | _ => addr  -- Not a REF, return as-is

/-! ## Unification Stack (PDL)

The PDL (Push-Down List) is used by the unification algorithm.
-/

abbrev PDL := List HeapAddr

/-- Empty unification stack -/
def PDL.empty : PDL := []

/-- Push two addresses onto PDL -/
def PDL.push2 (pdl : PDL) (a1 a2 : HeapAddr) : PDL := a2 :: a1 :: pdl

/-- Pop two addresses from PDL -/
def PDL.pop2 (pdl : PDL) : Option (HeapAddr × HeapAddr × PDL) :=
  match pdl with
  | a1 :: a2 :: rest => some (a1, a2, rest)
  | _ => none

end Mettapedia.AutoBooks.ClaudeProcWam.WAM
