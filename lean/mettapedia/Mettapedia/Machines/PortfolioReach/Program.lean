import Mettapedia.Machines.PortfolioReach.Embedding

/-!
# Relations with integer arithmetic, reads and writes

The generator of a take is a program of relations. An equation of a relation is a list of
goals over the relation's parameters and the values its earlier goals pushed, and an answer:

* `prim` applies an arithmetic primitive and pushes its value;
* `test` compares, and fails the alternative when the comparison is false;
* `call` enters a relation, one alternative per equation, and pushes the callee's answer;
* `read` pushes a row of a space, one alternative per row, in the order the store keeps;
* `write` adds a row to a space: an effect.

`system` is this language as a `System`: a fault is a raise, a write is an effect, and a read
reads the store of the moment.

The primitives follow CeTTa's number model on integers: the open tier's fast path on machine
integers (`oem_prim`) hands an overflow to exact big-integer arithmetic (`grounded.c`), so the
machine computes the exact result (`runPrim_int`). Hence `+`, `-`, `*`, `min` and `max` are
total on the integers (`total_int`), `%` is total off a zero divisor (`mod_int`), `/` and `%`
raise on a zero divisor, the four orders raise on a symbol, and `==` never raises.

The model's values are integers and symbols. Floats are outside it: in CeTTa a float operation
can raise (`(* 1.0e308 10.0)` and `(- inf inf)` do), and the symbols `inf`, `-inf`, `nan`, `pi`,
`e` and `epsilon` are floats at the arithmetic boundary (`(+ 1 pi)` answers). On an inexact
quotient CeTTa's `/` answers a float; the model stops there with the fault `inexact`. The fast
path's `%` is written with Lean's floored remainder; the C computes the truncated remainder and
moves it to the divisor's sign, which is the same number.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.PortfolioReach

/-! ## Values and integer arithmetic -/

/-- An integer (machine integers promote to big integers, so all of `ℤ`) or a symbol. -/
inductive Val where
  | int (value : Int)
  | sym (name : Nat)
  deriving DecidableEq, Repr

def Val.isInt : Val → Bool
  | .int _ => true
  | .sym _ => false

theorem Val.isInt_iff (value : Val) : value.isInt = true ↔ ∃ number, value = .int number := by
  cases value <;> simp [Val.isInt]

inductive Prim where
  | add | sub | mul | min | max | mod | div
  deriving DecidableEq, Repr

inductive Cmp where
  | lt | gt | le | ge | eq
  deriving DecidableEq, Repr

/-- Why a primitive raises. -/
inductive Fault where
  | typeError
  | zeroDivisor
  /-- A quotient that is not an integer: CeTTa answers a float, outside the model. -/
  | inexact
  deriving DecidableEq, Repr

/-- A machine integer. -/
def fits (value : Int) : Bool := decide (-2 ^ 63 ≤ value ∧ value < 2 ^ 63)

/-- The open tier's fast path on two machine integers: `none` hands the operation to the
grounded path, for an overflow or a zero divisor. -/
def fastPrim : Prim → Int → Int → Option Int
  | .add, a, b => if fits (a + b) then some (a + b) else none
  | .sub, a, b => if fits (a - b) then some (a - b) else none
  | .mul, a, b => if fits (a * b) then some (a * b) else none
  | .min, a, b => some (min a b)
  | .max, a, b => some (max a b)
  | .mod, a, b => if b = 0 then none else if b = -1 then some 0 else some (Int.fmod a b)
  | .div, _, _ => none

/-- The grounded path, on exact integers. `%` is the floored remainder. -/
def exactPrim : Prim → Int → Int → Except Fault Val
  | .add, a, b => .ok (.int (a + b))
  | .sub, a, b => .ok (.int (a - b))
  | .mul, a, b => .ok (.int (a * b))
  | .min, a, b => .ok (.int (min a b))
  | .max, a, b => .ok (.int (max a b))
  | .mod, a, b => if b = 0 then .error .zeroDivisor else .ok (.int (Int.fmod a b))
  | .div, a, b =>
      if b = 0 then .error .zeroDivisor
      else if a % b = 0 then .ok (.int (a / b)) else .error .inexact

/-- A primitive as the machine runs it: the fast path on machine integers when it answers,
the grounded path otherwise. Any other operand is a type error. -/
def runPrim (op : Prim) : Val → Val → Except Fault Val
  | .int a, .int b =>
      if fits a && fits b then
        match fastPrim op a b with
        | some result => .ok (.int result)
        | none => exactPrim op a b
      else exactPrim op a b
  | _, _ => .error .typeError

/-- **Promotion.** On integers the machine computes the exact primitive. -/
theorem runPrim_int (op : Prim) (a b : Int) :
    runPrim op (.int a) (.int b) = exactPrim op a b := by
  show (if fits a && fits b then
      match fastPrim op a b with
      | some result => .ok (.int result)
      | none => exactPrim op a b
    else exactPrim op a b) = exactPrim op a b
  split
  · cases op with
    | add => by_cases fit : fits (a + b) = true <;> simp [fastPrim, exactPrim, fit]
    | sub => by_cases fit : fits (a - b) = true <;> simp [fastPrim, exactPrim, fit]
    | mul => by_cases fit : fits (a * b) = true <;> simp [fastPrim, exactPrim, fit]
    | min => simp [fastPrim, exactPrim]
    | max => simp [fastPrim, exactPrim]
    | mod =>
        by_cases zero : b = 0
        · simp [fastPrim, zero]
        · by_cases negOne : b = -1
          · subst negOne
            have divides : (-1 : Int) ∣ a := ⟨-a, by ring⟩
            simp [fastPrim, exactPrim, Int.fmod_eq_zero_of_dvd divides]
          · simp [fastPrim, exactPrim, zero, negOne]
    | div => rfl
  · rfl

/-- The primitives total on the integers. -/
def Prim.total : Prim → Bool
  | .add | .sub | .mul | .min | .max => true
  | .mod | .div => false

/-- **Totality.** `+`, `-`, `*`, `min` and `max` never raise on integers, and answer one. -/
theorem total_int {op : Prim} (total : op.total = true) (a b : Int) :
    ∃ c, runPrim op (.int a) (.int b) = .ok (.int c) := by
  rw [runPrim_int]
  cases op <;> simp_all [Prim.total, exactPrim]

/-- `%` never raises on integers off a zero divisor. -/
theorem mod_int (a : Int) {b : Int} (nonzero : b ≠ 0) :
    runPrim .mod (.int a) (.int b) = .ok (.int (Int.fmod a b)) := by
  rw [runPrim_int]
  simp [exactPrim, nonzero]

/-- Comparisons: the four orders read integers, `==` compares any two values. -/
def runCmp : Cmp → Val → Val → Except Fault Bool
  | .eq, x, y => .ok (decide (x = y))
  | .lt, .int a, .int b => .ok (decide (a < b))
  | .gt, .int a, .int b => .ok (decide (b < a))
  | .le, .int a, .int b => .ok (decide (a ≤ b))
  | .ge, .int a, .int b => .ok (decide (b ≤ a))
  | _, _, _ => .error .typeError

theorem cmp_int (op : Cmp) (a b : Int) : ∃ truth, runCmp op (.int a) (.int b) = .ok truth := by
  cases op <;> simp [runCmp]

theorem eq_total (x y : Val) : runCmp .eq x y = .ok (decide (x = y)) := by
  cases x <;> cases y <;> rfl

/-! ## The language -/

inductive Operand where
  | var (index : Nat)
  | lit (value : Val)
  deriving DecidableEq, Repr

inductive Goal where
  | prim (op : Prim) (left right : Operand)
  | test (op : Cmp) (left right : Operand)
  | call (relation : Nat) (arguments : List Operand)
  | read (space : Nat)
  | write (space : Nat) (row : Operand)
  deriving DecidableEq, Repr

structure Equation where
  goals : List Goal
  result : Operand
  deriving DecidableEq, Repr

structure Relation where
  arity : Nat
  equations : List Equation
  deriving DecidableEq, Repr

/-- Relation `r` of a program is its `r`-th entry. -/
abbrev Program := List Relation

/-- An activation: its values (parameters first, then what its goals pushed), the goals left,
and its answer operand. -/
structure Frame where
  env : List Val
  goals : List Goal
  result : Operand
  deriving DecidableEq, Repr

/-- The rows of each space, in the order the store keeps them. -/
abbrev Store := Nat → List Val

inductive Event where
  | fault (fault : Fault)
  | add (space : Nat) (row : Val)
  deriving DecidableEq, Repr

def Operand.eval (env : List Val) : Operand → Val
  | .var index => env.getD index (.sym 0)
  | .lit value => value

/-- One step of a stack of activations, the newest first. -/
def stepFrames (program : Program) (store : Store) : List Frame → Move (List Frame) Val Event
  | [] => .branch []
  | frame :: rest =>
      match frame.goals with
      | [] =>
          match rest with
          | [] => .answer (frame.result.eval frame.env)
          | caller :: below =>
              .branch [{ caller with env := caller.env ++ [frame.result.eval frame.env] } :: below]
      | .prim op left right :: goals =>
          match runPrim op (left.eval frame.env) (right.eval frame.env) with
          | .ok value => .branch [⟨frame.env ++ [value], goals, frame.result⟩ :: rest]
          | .error fault => .raise (.fault fault)
      | .test op left right :: goals =>
          match runCmp op (left.eval frame.env) (right.eval frame.env) with
          | .ok true => .branch [⟨frame.env, goals, frame.result⟩ :: rest]
          | .ok false => .branch []
          | .error fault => .raise (.fault fault)
      | .call relation arguments :: goals =>
          match program[relation]? with
          | none => .branch []
          | some callee =>
              if arguments.length = callee.arity then
                .branch (callee.equations.map fun equation =>
                  ⟨arguments.map (Operand.eval frame.env), equation.goals, equation.result⟩ ::
                    ⟨frame.env, goals, frame.result⟩ :: rest)
              else .branch []
      | .read space :: goals =>
          .branch ((store space).map fun row => ⟨frame.env ++ [row], goals, frame.result⟩ :: rest)
      | .write space row :: goals =>
          .effect (.add space (row.eval frame.env)) (⟨frame.env, goals, frame.result⟩ :: rest)

def applyEvent : Event → Store → Store
  | .add space row, store => Function.update store space (store space ++ [row])
  | .fault _, store => store

def system (program : Program) : System Store (List Frame) Val Event where
  expand := stepFrames program
  apply := applyEvent

/-- The stack a take of relation `entry` on `arguments` starts from. -/
def root (entry : Nat) (arguments : List Val) : List Frame :=
  [⟨[], [.call entry (arguments.map .lit)], .var 0⟩]

/-- A root with a reachable state that is not quiet is not quiet. -/
theorem not_quiet {program : Program} {store : Store} {start : List Frame}
    {children : List (List Frame)} {state : List Frame}
    (expands : ((system program).space store).expand start = .branch children)
    (member : state ∈ children)
    (loud : ((system program).expand store state).quiet = false) :
    ¬ Quiet (system program) store start := by
  intro quiet
  have here := quiet state (.step expands member (.here state))
  rw [loud] at here
  cases here

namespace Controls

/-- A machine-integer overflow goes to the grounded path and is exact, as CeTTa answers
`9223372036854775808` for `(+ 9223372036854775807 1)` and for `(* -9223372036854775808 -1)`. -/
theorem promotion :
    fastPrim .add (2 ^ 63 - 1) 1 = none ∧
      runPrim .add (.int (2 ^ 63 - 1)) (.int 1) = .ok (.int (2 ^ 63)) ∧
      runPrim .mul (.int (-2 ^ 63)) (.int (-1)) = .ok (.int (2 ^ 63)) := by decide

/-- `%` is the floored remainder, as CeTTa answers `1` for `(% -7 2)`, `-1` for `(% 7 -2)` and
`0` for `(% 5 -1)`. -/
theorem floored_remainder :
    runPrim .mod (.int (-7)) (.int 2) = .ok (.int 1) ∧
      runPrim .mod (.int 7) (.int (-2)) = .ok (.int (-1)) ∧
      runPrim .mod (.int 5) (.int (-1)) = .ok (.int 0) := by decide

/-- A zero divisor raises, as CeTTa raises `zero_divisor` for `(/ 1 0)` and `(% 1 0)`. -/
theorem zero_divisor :
    runPrim .div (.int 1) (.int 0) = .error .zeroDivisor ∧
      runPrim .mod (.int 1) (.int 0) = .error .zeroDivisor := by decide

/-- `/` leaves the integers on an inexact quotient (CeTTa answers `3.5` for `(/ 7 2)`). -/
theorem inexact_quotient :
    runPrim .div (.int 7) (.int 2) = .error .inexact ∧
      runPrim .div (.int 6) (.int 2) = .ok (.int 3) := by decide

/-- A symbol operand raises in arithmetic and in an order, not in `==`, as CeTTa raises for
`(+ 1 a)` and `(< a 1)` and answers `false` for `(== a 1)`. -/
theorem symbol_operands :
    runPrim .add (.int 1) (.sym 0) = .error .typeError ∧
      runCmp .lt (.sym 0) (.int 1) = .error .typeError ∧
      runCmp .eq (.sym 0) (.int 1) = .ok false := by decide

end Controls

#print axioms runPrim_int
#print axioms total_int
#print axioms mod_int
#print axioms cmp_int
#print axioms eq_total
#print axioms Controls.promotion
#print axioms Controls.zero_divisor

end Mettapedia.Machines.PortfolioReach
