import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ComputedConditions.MachineInvariants

/-!
# The machine at 64-bit words: a run, a refusal, and the control for the trusted operations

`Machine` is stated over any type of words with an encoding into rows. Here it is instantiated.

* `wordsBelow N`: the words below a bound, each the numeral of its value; a row that is no numeral below the
  bound encodes no word. `words64` is the instance at `2^64`.
* `ops64`: **two operations with two outputs**: addition modulo `2^64` with its carry (total), and division with
  remainder, which has **no value** at divisor zero.
* `demo`: a store with two registers holding `2^64 - 1` and `1` and three instructions:
  `r0 := r0 + r1`; `r1 := r1 + r1` (its source is its destination); `r1 := r1 / r0`.
  - `demo_step`, `demo1_step`: the machine makes two transitions: the first wraps to `0` with carry `1`, the
    second doubles register `1` by the rule for a source that is the destination.
  - `demo2_refuses`: at the third instruction the divisor is `0`, the operation has no value, and the machine
    has no transition.
  - `demo_run`, `demo_stuck`: so, from every state that reads as the rows of `demo`, the evaluated program has a
    run of two firings to a state that reads as the rows of the store after them, and every state that reads as
    those rows is stuck. Such a state exists (`Machine.exists_state`).
* **Control for the trusted operations** (`wrongOps`, `wrong_step`, `wrong_value_made`, `wrong_rows_differ`):
  the theorems follow the operations they are given. With an addition that is off by one and nothing else
  changed, the same instruction at the same state is admitted and its result reads as the rows of a store whose
  register `0` holds `1`, which are not the rows of the store the true operation gives. What is trusted is the
  table of operations with the encoding of words, together with the hypothesis that the state reads as the rows
  of a store.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ComputedConditions.Machine

open Mettapedia.Logic.LP
open Mettapedia.GSLT
open NamesOnTheStep (Expr)
open Presentation.Schematic (Tm SState X E)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Machines (ReadsBag)

/-! ## Words below a bound -/

/-- **The words below a bound, as rows**: a word is the numeral of its value. -/
def wordsBelow (N : ℕ) : Words (Fin N) where
  enc w := .sym w.val
  dec x :=
    match x with
    | .sym n => if below : n < N then some ⟨n, below⟩ else none
    | _ => none
  dec_enc w := by
    show (if below : w.val < N then some (⟨w.val, below⟩ : Fin N) else none) = some w
    rw [dif_pos w.isLt]
  enc_dec := by
    intro x w decoded
    cases x with
    | sym n =>
        change (if below : n < N then some (⟨n, below⟩ : Fin N) else none) = some w at decoded
        by_cases below : n < N
        · rw [dif_pos below] at decoded
          rw [← Option.some.inj decoded]
        · rw [dif_neg below] at decoded
          cases decoded
    | app _ _ =>
        change (none : Option (Fin N)) = some w at decoded
        cases decoded
    | name _ =>
        change (none : Option (Fin N)) = some w at decoded
        cases decoded
    | code _ =>
        change (none : Option (Fin N)) = some w at decoded
        cases decoded

/-- **64-bit words.** -/
abbrev Word64 : Type := Fin (2 ^ 64)

/-- **64-bit words as rows.** -/
def words64 : Words Word64 := wordsBelow (2 ^ 64)

/-- A 64-bit word from a numeral below the bound. -/
abbrev w64 (n : ℕ) (below : n < 2 ^ 64 := by decide) : Word64 := ⟨n, below⟩

/-! ## Two operations -/

/-- The operation code of addition with carry. -/
abbrev addOp : ℕ := 10

/-- The operation code of division with remainder. -/
abbrev divOp : ℕ := 11

/-- **Two operations on 64-bit words, each with two outputs**: addition modulo `2^64` with its carry, and division
with remainder, which has no value at divisor zero. -/
def ops64 : ℕ → Word64 → Word64 → Option (Word64 × Word64) := fun f a b =>
  if f = addOp then some (a + b, if a.val + b.val < 2 ^ 64 then w64 0 else w64 1)
  else if f = divOp then (if b.val = 0 then none else some (a / b, a % b))
  else none

/-! ## A store, two transitions and a refusal -/

/-- **A store**: counter `0`; registers `0` and `1` holding `2^64 - 1` and `1`; the flag `0`; the table
`0: r0 := r0 + r1`, `1: r1 := r1 + r1`, `2: r1 := r1 / r0`. -/
def demo : Store Word64 where
  pc := 0
  flag := w64 0
  regs := {0, 1}
  reg := fun key => if key = 0 then w64 (2 ^ 64 - 1) else w64 1
  points := {0, 1, 2}
  code := fun p => if p = 0 then ⟨addOp, 0, 1, 1⟩ else if p = 1 then ⟨addOp, 1, 1, 2⟩ else ⟨divOp, 1, 0, 3⟩

/-- The store after the first instruction: register `0` holds `0`, the flag `1`. -/
def demo1 : Store Word64 := after demo (w64 0) (w64 1)

/-- The store after the second instruction: register `1` holds `2`, the flag `0`. -/
def demo2 : Store Word64 := after demo1 (w64 2) (w64 0)

/-- **The first transition**: `(2^64 - 1) + 1` is `0` with carry `1`. -/
theorem demo_step : Steps ops64 demo demo1 :=
  ⟨by decide, by decide, by decide, w64 0, w64 1, by decide, rfl⟩

/-- **The second transition**, at an instruction whose source is its destination: `1 + 1` is `2` with carry
`0`. -/
theorem demo1_step : Steps ops64 demo1 demo2 :=
  ⟨by decide, by decide, by decide, w64 2, w64 0, by decide, rfl⟩

/-- The second instruction's source is its destination. -/
theorem demo1_same : (demo1.code demo1.pc).src = (demo1.code demo1.pc).dst := by decide

/-- **The machine refuses the third instruction**: the divisor is `0` and the operation has no value. -/
theorem demo2_refuses : ¬ ∃ m', Steps ops64 demo2 m' :=
  (no_step_iff ops64 demo2).mpr (.inr (.inr (.inr (by decide))))

section States

variable {O : Type} [DecidableEq O]

/-- **The evaluated program runs the two instructions**, from every state that reads as the rows of the store,
to a state that reads as the rows of the store after them. -/
theorem demo_run [Infinite O] {s : SState O} (reads : ReadsBag s (storeRows words64 demo)) :
    ∃ s', (programSystem O (evaluated (interp words64 ops64) program)).MultiStep s s' ∧
      ReadsBag s' (storeRows words64 demo2) :=
  runs_of_machine words64 ops64 reads (.step demo_step (.step demo1_step (.refl _)))

/-- **Every state that reads as the rows of the store after them is stuck**: the operation has no value. -/
theorem demo_stuck [Infinite O] {s : SState O} (reads : ReadsBag s (storeRows words64 demo2)) :
    ¬ ∃ f : Firing O E (evaluated (interp words64 ops64) program) s.frame,
      (step X O E (evaluated (interp words64 ops64) program)).Admits (s := s) f :=
  (stuck_iff words64 ops64 reads).mpr demo2_refuses

/-! ## Control: a wrong operation makes its wrong value -/

/-- **A wrong table of operations**: addition is off by one; nothing else is changed. -/
def wrongOps : ℕ → Word64 → Word64 → Option (Word64 × Word64) := fun f a b =>
  if f = addOp then some (a + b + w64 1, if a.val + b.val < 2 ^ 64 then w64 0 else w64 1) else ops64 f a b

/-- The store the wrong addition gives: register `0` holds `1`. -/
def demoWrong : Store Word64 := after demo (w64 1) (w64 1)

/-- The machine of the wrong operations makes the wrong transition. -/
theorem wrong_step : Steps wrongOps demo demoWrong :=
  ⟨by decide, by decide, by decide, w64 1, w64 1, by decide, rfl⟩

/-- **With the wrong operation, the same instruction at the same state is admitted and makes the wrong value**:
its result reads as the rows of the store whose register `0` holds `1`. -/
theorem wrong_value_made [Infinite O] {s : SState O} (reads : ReadsBag s (storeRows words64 demo)) :
    ∃ (f : Firing O E (evaluated (interp words64 wrongOps) program) s.frame)
      (_ : (step X O E (evaluated (interp words64 wrongOps) program)).Admits (s := s) f),
      ReadsBag (f.result X s) (storeRows words64 demoWrong) :=
  machine_forward words64 wrongOps reads wrong_step

end States

/-- **The wrong rows are not the right rows**: the cell of register `0` holding `1` is a row of the wrong store
and no row of the store the true operation gives. -/
theorem wrong_rows_differ : storeRows words64 demoWrong ≠ storeRows words64 demo1 := by
  intro same
  have rows := storeRows_after words64 demo (w64 1) (w64 1) (by decide)
  have inWrong : regRow 0 (words64.enc (w64 1)) ∈ storeRows words64 demoWrong := by
    have inRows : regRow 0 (words64.enc (w64 1)) ∈ storeRows words64 (after demo (w64 1) (w64 1)) := by
      rw [rows]
      exact Multiset.mem_add.mpr (.inl (Multiset.mem_coe.mpr (List.mem_cons_of_mem _ List.mem_cons_self)))
    exact inRows
  rw [same] at inWrong
  rcases cell_of_mem_storeRows words64 demo1 inWrong with ⟨kind, -, -⟩ | ⟨kind, -, -⟩ | ⟨d, -, -, key, value⟩
  · exact absurd (Expr.sym.inj kind) (by decide)
  · exact absurd (Expr.sym.inj kind) (by decide)
  · have isZero : d = 0 := (Expr.sym.inj key).symm
    subst isZero
    exact absurd (words64.enc_injective value) (by decide)

#print axioms wordsBelow
#print axioms demo_step
#print axioms demo1_step
#print axioms demo2_refuses
#print axioms demo_run
#print axioms demo_stuck
#print axioms wrong_step
#print axioms wrong_value_made
#print axioms wrong_rows_differ

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ComputedConditions.Machine
