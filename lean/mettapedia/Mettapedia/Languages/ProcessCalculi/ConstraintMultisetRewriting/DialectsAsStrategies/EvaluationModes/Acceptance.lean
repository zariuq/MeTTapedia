import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.EvaluationModes.Designs

/-!
# Acceptance: each design's elaboration on the measured programs

The eight programs of the measured table, with `(= (f a) 5)` in each, written in the surface and
run through each design's elaboration by kernel evaluation (`decide +kernel`):

1. `(: g (-> Atom Atom)) (= (g $x) $x)`, `!(g (f a))`;
2. the same under `Number`, `%Undefined%`, a type variable;
3. the same under `Proc`;
4. `!(let $y (held-atom (f a)) $y)` with `held-atom` the program of row 1;
5. `!(compute (held-atom (f a)))` with `(: compute (-> T T)) (= (compute $x) $x)`,
   `T = %Undefined%` (Hyperon Experimental, PeTTa) or `Proc` (Prime);
6. `(: hu-wrap (-> Atom %Undefined%)) (= (hu-wrap $x) (wrap $x))`, `!(hu-wrap (f a))`;
7. `(: mk (-> Number Atom)) (= (mk $n) (pair $n (+ $n 1)))`, `!(mk 3)`;
8. `(: my-if (-> Bool Atom Atom %Undefined%))` with its two equations, `!(my-if True (f a) (boom))`.

Measured (12 November; Hyperon Experimental's `metta-repl`, CeTTa's PeTTa lane, the Prime draft):

| row | HE | PeTTa | Prime |
|---|---|---|---|
| 1 | `(f a)` | `(f a)` | `(f a)` |
| 2 | `5` `5` `5` | none, `(f a)`, `(f a)` | `5` `5` `5` |
| 3 | no `Proc` type | no `Proc` type | `5` |
| 4 | `5` | `(f a)` | `(f a)` |
| 5 | `5` | `(f a)` | `(f a)` |
| 6 | `(wrap 5)` | `(wrap (f a))` | `(wrap (f a))` |
| 7 | `(pair 3 (+ 3 1))` | `(pair 3 (+ 3 1))` | `(pair 3 4)` |
| 8 | `5` | `(f a)` | `5` |

`he_column`, `codeValue_column` and `primeToday_column` give exactly these columns: the model of
each design reproduces its system on every measured row. `byName_column` and `hybrid_column` are
the two designs with no implementation; `hybrid_prime_tests` shows the hybrid passing the three
Prime test lines it was made for.

Further rows measured for this study (`further_rows`): a held parameter passed to an evaluated
identity, used as a `let` source, or as a field twice; on these too each model gives its system's
answer. One measured row lies outside the core: `(+ $x 1)` on a held `(f a)` is a fault in PeTTa,
while the core's `+` returns the unreduced call, which is Prime's answer; `plus_row` records the
models' answers and the difference.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.EvaluationModes

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open Core

namespace Acceptance

/-- A symbol. -/
def S (s : String) : Atom := .symbol s
/-- An integer. -/
def N (n : Int) : Atom := .grounded (.int n)
/-- A variable. -/
def V (x : String) : Atom := .var x
/-- An expression. -/
def E (items : List Atom) : Atom := .expression items

/-- `(= (f a) 5)`. -/
def fA : Fn := ⟨"f", none, [([S "a"], N 5)]⟩

/-- `(f a)`. -/
def callFA : Atom := E [S "f", S "a"]

/-- `(: g (-> Atom R)) (= (g $x) $x)`. -/
def heldId (g : String) (R : Ty) : Fn := ⟨g, some ([.atom], R), [([V "x"], V "x")]⟩

/-- `(: g (-> T T)) (= (g $x) $x)` for an evaluated parameter type `T`. -/
def valueId (g : String) (T : Ty) : Fn := ⟨g, some ([T], T), [([V "x"], V "x")]⟩

/-- Rows 1–3: the held identity under result type `R`. -/
def rangeProg (R : Ty) : SProg := [fA, heldId "g" R]

/-- `(g (f a))`. -/
def qRange : Atom := E [S "g", callFA]

/-- Row 4. -/
def letProg : SProg := [fA, heldId "held-atom" .atom]

/-- `(let $y (held-atom (f a)) $y)`. -/
def qLet : Atom := E [S "let", V "y", E [S "held-atom", callFA], V "y"]

/-- Row 5, with `compute` typed `(-> T T)`. -/
def computeProg (T : Ty) : SProg := [fA, heldId "held-atom" .atom, valueId "compute" T]

/-- `(compute (held-atom (f a)))`. -/
def qCompute : Atom := E [S "compute", E [S "held-atom", callFA]]

/-- Row 6. -/
def wrapProg : SProg := [fA, ⟨"hu-wrap", some ([.atom], .undef), [([V "x"], E [S "wrap", V "x"])]⟩]

/-- `(hu-wrap (f a))`. -/
def qWrap : Atom := E [S "hu-wrap", callFA]

/-- Row 7. -/
def mkProg : SProg :=
  [⟨"mk", some ([.number], .atom), [([V "n"], E [S "pair", V "n", E [S "+", V "n", N 1]])]⟩]

/-- `(mk 3)`. -/
def qMk : Atom := E [S "mk", N 3]

/-- HE's `if` written as a function: `(: my-if (-> Bool Atom Atom R))` and its two equations. -/
def myIf (R : Ty) : Fn :=
  ⟨"my-if", some ([.bool, .atom, .atom], R),
    [([S "True", V "t", V "e"], V "t"), ([S "False", V "t", V "e"], V "e")]⟩

/-- Row 8. -/
def ifProg : SProg := [fA, myIf .undef]

/-- `(my-if True (f a) (boom))`. -/
def qIf : Atom := E [S "my-if", S "True", callFA, E [S "boom"]]

/-- Fuel for every run here; each run below finishes well within it. -/
def F : Nat := 40

/-! ## The measured columns -/

/-- **Hyperon Experimental's column.** -/
theorem he_column :
    answers he (rangeProg .atom) F qRange = some [callFA] ∧
    answers he (rangeProg .number) F qRange = some [N 5] ∧
    answers he (rangeProg .undef) F qRange = some [N 5] ∧
    answers he (rangeProg .tvar) F qRange = some [N 5] ∧
    answers he letProg F qLet = some [N 5] ∧
    answers he (computeProg .undef) F qCompute = some [N 5] ∧
    answers he wrapProg F qWrap = some [E [S "wrap", N 5]] ∧
    answers he mkProg F qMk = some [E [S "pair", N 3, E [S "+", N 3, N 1]]] ∧
    answers he ifProg F qIf = some [N 5] := by
  decide +kernel

/-- **PeTTa's column** is the code-value design's: under `Number` the returned text is refused and
PeTTa prints no answer. -/
theorem codeValue_column :
    answers codeValue (rangeProg .atom) F qRange = some [callFA] ∧
    answers codeValue (rangeProg .number) F qRange = some [] ∧
    answers codeValue (rangeProg .undef) F qRange = some [callFA] ∧
    answers codeValue (rangeProg .tvar) F qRange = some [callFA] ∧
    answers codeValue letProg F qLet = some [callFA] ∧
    answers codeValue (computeProg .undef) F qCompute = some [callFA] ∧
    answers codeValue wrapProg F qWrap = some [E [S "wrap", callFA]] ∧
    answers codeValue mkProg F qMk = some [E [S "pair", N 3, E [S "+", N 3, N 1]]] ∧
    answers codeValue ifProg F qIf = some [callFA] := by
  decide +kernel

/-- **The Prime draft's column.** -/
theorem primeToday_column :
    answers primeToday (rangeProg .atom) F qRange = some [callFA] ∧
    answers primeToday (rangeProg .number) F qRange = some [N 5] ∧
    answers primeToday (rangeProg .undef) F qRange = some [N 5] ∧
    answers primeToday (rangeProg .tvar) F qRange = some [N 5] ∧
    answers primeToday (rangeProg .proc) F qRange = some [N 5] ∧
    answers primeToday letProg F qLet = some [callFA] ∧
    answers primeToday (computeProg .proc) F qCompute = some [callFA] ∧
    answers primeToday wrapProg F qWrap = some [E [S "wrap", callFA]] ∧
    answers primeToday mkProg F qMk = some [E [S "pair", N 3, N 4]] ∧
    answers primeToday ifProg F qIf = some [N 5] := by
  decide +kernel

/-- The by-name design on the same rows: HE's answers except where HE runs a value again (rows 4
and 5). -/
theorem byName_column :
    answers byName (rangeProg .atom) F qRange = some [callFA] ∧
    answers byName (rangeProg .number) F qRange = some [N 5] ∧
    answers byName (rangeProg .undef) F qRange = some [N 5] ∧
    answers byName (rangeProg .tvar) F qRange = some [N 5] ∧
    answers byName (rangeProg .proc) F qRange = some [N 5] ∧
    answers byName letProg F qLet = some [callFA] ∧
    answers byName (computeProg .proc) F qCompute = some [callFA] ∧
    answers byName wrapProg F qWrap = some [E [S "wrap", N 5]] ∧
    answers byName mkProg F qMk = some [E [S "pair", N 3, E [S "+", N 3, N 1]]] ∧
    answers byName ifProg F qIf = some [N 5] := by
  decide +kernel

/-- The withdrawn hybrid on the same rows: the Prime draft's answers except under `Proc`. -/
theorem hybrid_column :
    answers hybrid (rangeProg .atom) F qRange = some [callFA] ∧
    answers hybrid (rangeProg .number) F qRange = some [N 5] ∧
    answers hybrid (rangeProg .undef) F qRange = some [N 5] ∧
    answers hybrid (rangeProg .tvar) F qRange = some [N 5] ∧
    answers hybrid (rangeProg .proc) F qRange = some [callFA] ∧
    answers hybrid letProg F qLet = some [callFA] ∧
    answers hybrid (computeProg .proc) F qCompute = some [callFA] ∧
    answers hybrid wrapProg F qWrap = some [E [S "wrap", callFA]] ∧
    answers hybrid mkProg F qMk = some [E [S "pair", N 3, N 4]] ∧
    answers hybrid ifProg F qIf = some [N 5] := by
  decide +kernel

/-- Row 5 does not depend on whether `compute` is typed `Proc` or `%Undefined%`, in any named
design. -/
theorem compute_proc_eq_undef :
    answers he (computeProg .proc) F qCompute = answers he (computeProg .undef) F qCompute ∧
    answers codeValue (computeProg .proc) F qCompute =
      answers codeValue (computeProg .undef) F qCompute ∧
    answers primeToday (computeProg .proc) F qCompute =
      answers primeToday (computeProg .undef) F qCompute := by
  decide +kernel

/-! ## The three Prime test lines -/

/-- `tests/prime/held_arguments`: `(: held-undefined (-> Atom %Undefined%))` on `(f a)` gives `5`. -/
def testUndefProg : SProg := [fA, heldId "held-undefined" .undef]

/-- `(held-undefined (f a))`. -/
def testUndefQuery : Atom := E [S "held-undefined", callFA]

/-- `tests/prime/atom_result_type`: `(: held (-> Atom Proc))` on `(+ 1 2)` gives `(+ 1 2)`. -/
def testProcProg : SProg := [heldId "held" .proc]

/-- `(held (+ 1 2))`. -/
def testProcQuery : Atom := E [S "held", E [S "+", N 1, N 2]]

/-- `tests/prime/atom_proc_roles`: `(: roles:changing (-> Atom Proc))` on `(+ 4 5)` gives
`(+ 4 5)`. -/
def testRolesProg : SProg := [heldId "roles:changing" .proc]

/-- `(roles:changing (+ 4 5))`. -/
def testRolesQuery : Atom := E [S "roles:changing", E [S "+", N 4, N 5]]

/-- The three lines' expected answers. -/
def PassesPrimeTests (D : Design) : Prop :=
  answers D testUndefProg F testUndefQuery = some [N 5] ∧
  answers D testProcProg F testProcQuery = some [E [S "+", N 1, N 2]] ∧
  answers D testRolesProg F testRolesQuery = some [E [S "+", N 4, N 5]]

/-- The hybrid passes all three lines. -/
theorem hybrid_prime_tests : PassesPrimeTests hybrid := by
  unfold PassesPrimeTests
  decide +kernel

/-- The Prime draft fails the two `Proc` lines (it answers `3` and `9`), as measured. -/
theorem primeToday_prime_tests :
    answers primeToday testUndefProg F testUndefQuery = some [N 5] ∧
    answers primeToday testProcProg F testProcQuery = some [N 3] ∧
    answers primeToday testRolesProg F testRolesQuery = some [N 9] := by
  decide +kernel

/-! ## Further measured rows -/

/-- `(: twice (-> Atom %Undefined%)) (= (twice $x) (pair $x $x))`. -/
def twiceProg : SProg := [fA, ⟨"twice", some ([.atom], .undef), [([V "x"], E [S "pair", V "x", V "x"])]⟩]

/-- `(twice (f a))`. -/
def qTwice : Atom := E [S "twice", callFA]

/-- A held parameter passed to an evaluated identity: `(= (via-id $x) (myid $x))`. -/
def viaIdProg (T : Ty) : SProg :=
  [fA, valueId "myid" T, ⟨"via-id", some ([.atom], T), [([V "x"], E [S "myid", V "x"])]⟩]

/-- `(via-id (f a))`. -/
def qViaId : Atom := E [S "via-id", callFA]

/-- A held parameter as a `let` source: `(= (via-let $x) (let $y $x $y))`. -/
def viaLetProg (T : Ty) : SProg :=
  [fA, ⟨"via-let", some ([.atom], T), [([V "x"], E [S "let", V "y", V "x", V "y"])]⟩]

/-- `(via-let (f a))`. -/
def qViaLet : Atom := E [S "via-let", callFA]

/-- A written constructor call: `!(wrap (f a))`. -/
def qWrapWritten : Atom := E [S "wrap", callFA]

/-- Measured: HE `(pair 5 5)`, `5`, `5`, `(wrap 5)`; PeTTa `(pair (f a) (f a))`, `(f a)`, `(f a)`,
`(wrap 5)`; Prime `(pair (f a) (f a))`, `(f a)`, `(f a)`, `(wrap 5)`. -/
theorem further_rows :
    answers he twiceProg F qTwice = some [E [S "pair", N 5, N 5]] ∧
    answers he (viaIdProg .undef) F qViaId = some [N 5] ∧
    answers he (viaLetProg .undef) F qViaLet = some [N 5] ∧
    answers he [fA] F qWrapWritten = some [E [S "wrap", N 5]] ∧
    answers codeValue twiceProg F qTwice = some [E [S "pair", callFA, callFA]] ∧
    answers codeValue (viaIdProg .undef) F qViaId = some [callFA] ∧
    answers codeValue (viaLetProg .undef) F qViaLet = some [callFA] ∧
    answers codeValue [fA] F qWrapWritten = some [E [S "wrap", N 5]] ∧
    answers primeToday twiceProg F qTwice = some [E [S "pair", callFA, callFA]] ∧
    answers primeToday (viaIdProg .proc) F qViaId = some [callFA] ∧
    answers primeToday (viaLetProg .proc) F qViaLet = some [callFA] ∧
    answers primeToday [fA] F qWrapWritten = some [E [S "wrap", N 5]] := by
  decide +kernel

/-- `(= (via-plus $x) (+ $x 1))` on a held `(f a)`: HE `6` and the Prime draft `(+ (f a) 1)`, as
measured; the code-value model answers `(+ (f a) 1)` where PeTTa stops at a fault, a difference of
the grounded `+`, not of the evaluation mode. -/
def plusProg (T : Ty) : SProg :=
  [fA, ⟨"via-plus", some ([.atom], T), [([V "x"], E [S "+", V "x", N 1])]⟩]

/-- `(via-plus (f a))`. -/
def qPlus : Atom := E [S "via-plus", callFA]

theorem plus_row :
    answers he (plusProg .undef) F qPlus = some [N 6] ∧
    answers primeToday (plusProg .proc) F qPlus = some [E [S "+", callFA, N 1]] ∧
    answers codeValue (plusProg .undef) F qPlus = some [E [S "+", callFA, N 1]] := by
  decide +kernel

end Acceptance

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.EvaluationModes
