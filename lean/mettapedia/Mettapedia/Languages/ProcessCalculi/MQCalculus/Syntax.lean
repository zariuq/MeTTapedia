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
       | MQGate s P           -- named gate, then continue P
       | MQOut i              -- emit qubit i
       | MQIn i P Q           -- measure wire i: outcome 0 → P, outcome 1 → Q
```

Gate targets are encoded in the string spec (`"H@2"`, `"X@0"`, `"Z@5"`).
Legacy gate names (`"H"`, `"X"`, `"Z"`) default to wire `0`.
Concrete gate matrices live in `Backend.lean` and denotation in `Denotational.lean`.

## References

- Stay & Meredith (2026), Section 2
-/

namespace Mettapedia.Languages.ProcessCalculi.MQCalculus

/-- MQ-calculus processes with de Bruijn wire indices. -/
inductive Process : Type where
  | MQNil  : Process
  | MQPar  : Process → Process → Process
  | MQNu   : Process → Process
  /-- Named gate (identified by string), then continue. -/
  | MQGate : String → Process → Process
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
private def ex_hadamard  : Process := MQGate "H" MQNil

/-! ## Basic simp lemmas -/

@[simp] theorem isNil_MQNil : (MQNil : Process).isNil = true := rfl
@[simp] theorem isNil_MQPar (p q : Process) : (p ‖ q).isNil = false := rfl
@[simp] theorem isNil_MQNu  (p : Process)   : (MQNu p).isNil = false := rfl
@[simp] theorem isNil_MQOut (i : ℕ)         : (MQOut i).isNil = false := rfl
@[simp] theorem isNil_MQGate (s : String) (p : Process) :
    (MQGate s p).isNil = false := rfl
@[simp] theorem isNil_MQIn (i : ℕ) (p q : Process) : (MQIn i p q).isNil = false := rfl

end Process

end Mettapedia.Languages.ProcessCalculi.MQCalculus
