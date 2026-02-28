import Mathlib.Data.List.Basic

/-!
# MQ-Calculus: Syntax (De Bruijn)

Process grammar of the MQ-calculus following Stay & Meredith (2026), Section 2.

## De Bruijn convention

`MQNu P` allocates a fresh wire at index 0 and shifts all existing indices up by one.

## Grammar

```
P, Q ::= MQNil               -- stopped
       | MQPar P Q            -- parallel composition
       | MQNu P               -- new-wire binder (wire 0 = fresh)
       | MQGate g P           -- typed gate spec, then continue P
       | MQOut i              -- emit qubit i
       | MQIn i P Q           -- measure wire i: outcome 0 → P, outcome 1 → Q
```

Gate targets are typed (`GateSpec`) instead of encoded in free-form strings.
A compatibility parser `gateSpecOfString` accepts legacy forms such as `"H"`
and target forms such as `"X@2"`.

## References

- Stay & Meredith (2026), Section 2
-/

namespace Mettapedia.Languages.ProcessCalculi.MQCalculus

/-- Primitive one-qubit gate operators used by MQ examples. -/
inductive GateOp : Type where
  | H
  | X
  | Z
  | custom (name : String)
  deriving DecidableEq, Repr

/-- A typed gate specification: operation + target wire index. -/
structure GateSpec where
  op : GateOp
  target : ℕ
  deriving DecidableEq, Repr

namespace GateSpec

/-- Readable constructors for common gates. -/
def H (i : ℕ := 0) : GateSpec := ⟨.H, i⟩
def X (i : ℕ := 0) : GateSpec := ⟨.X, i⟩
def Z (i : ℕ := 0) : GateSpec := ⟨.Z, i⟩
def custom (name : String) (i : ℕ := 0) : GateSpec := ⟨.custom name, i⟩

/-- Render operation name for diagnostics/interchange. -/
def opName : GateOp → String
  | .H => "H"
  | .X => "X"
  | .Z => "Z"
  | .custom s => s

/-- Parse operation token from text. -/
def parseOp (s : String) : GateOp :=
  match s with
  | "H" => .H
  | "X" => .X
  | "Z" => .Z
  | _ => .custom s

/-- Parse a gate spec from `NAME` or `NAME@i` (legacy-friendly). -/
def ofString (gate : String) : GateSpec :=
  match gate.splitOn "@" with
  | [name] => ⟨parseOp name, 0⟩
  | [name, idx] => ⟨parseOp name, idx.toNat?.getD 0⟩
  | name :: _ => ⟨parseOp name, 0⟩
  | [] => ⟨parseOp gate, 0⟩

/-- Render to `NAME@i` (or just `NAME` when target is 0). -/
def render (g : GateSpec) : String :=
  let name := opName g.op
  if g.target = 0 then name else name ++ "@" ++ Nat.repr g.target

end GateSpec

/-- Backward-compatible alias used by external text-based pipelines. -/
def gateSpecOfString : String → GateSpec := GateSpec.ofString

/-- MQ-calculus processes with de Bruijn wire indices. -/
inductive Process : Type where
  | MQNil  : Process
  | MQPar  : Process → Process → Process
  | MQNu   : Process → Process
  /-- Typed gate spec, then continue. -/
  | MQGate : GateSpec → Process → Process
  | MQOut  : ℕ → Process
  | MQIn   : ℕ → Process → Process → Process
  deriving DecidableEq, Repr

namespace Process

/-- Parallel composition notation (mirrors PiCalculus ` ||| `). -/
infixl:60 " ‖ " => Process.MQPar

/-! ## Basic derived functions -/

/-- Is the process structurally nil? -/
def isNil : Process → Bool
  | MQNil => true
  | _     => false

/-- Number of top-level parallel components. -/
def parallelWidth : Process → ℕ
  | MQPar l r => parallelWidth l + parallelWidth r
  | _         => 1

/-! ## Examples -/

private def ex_nil       : Process := MQNil
private def ex_out0      : Process := MQOut 0
private def ex_in0       : Process := MQIn 0 MQNil MQNil
private def ex_new_out   : Process := MQNu (MQOut 0)
private def ex_comm_pair : Process := MQNu (MQOut 0 ‖ MQIn 0 MQNil MQNil)
private def ex_hadamard  : Process := MQGate (GateSpec.H 0) MQNil

/-! ## Basic simp lemmas -/

@[simp] theorem isNil_MQNil : (MQNil : Process).isNil = true := rfl
@[simp] theorem isNil_MQPar (p q : Process) : (p ‖ q).isNil = false := rfl
@[simp] theorem isNil_MQNu  (p : Process)   : (MQNu p).isNil = false := rfl
@[simp] theorem isNil_MQOut (i : ℕ)         : (MQOut i).isNil = false := rfl
@[simp] theorem isNil_MQGate (g : GateSpec) (p : Process) :
    (MQGate g p).isNil = false := rfl
@[simp] theorem isNil_MQIn (i : ℕ) (p q : Process) : (MQIn i p q).isNil = false := rfl

end Process

end Mettapedia.Languages.ProcessCalculi.MQCalculus
