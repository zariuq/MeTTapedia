import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ComputedConditions.Runs

/-!
# A register machine whose step rule evaluates its operation: the runs are the reference machine's runs

A small machine in the shape of a kernel that fires one rule per instruction and lets the rule compute its
value: a counter, a flag, registers and an instruction table. An instruction `(op, dst, src, next)` at the
counter performs `(dst, flag) := op(dst, src)` and moves the counter to `next`. Every operation has **two
outputs**, an operation may be **partial** (no value at some arguments), and the destination is always a
source.

## The reference machine

* `Store W`: the counter, the flag, the registers (a finite set of keys with their words) and the instruction
  table (a finite set of counters with their instructions), over any type `W` of words.
* `Steps ops m m'`: **one transition**: the counter holds an instruction, its two registers exist, the operation
  has a value `(r, c)` at the words the two registers hold, and `m'` is `m` with the destination holding `r`,
  the flag `c` and the counter at `next` (`after`). It is a partial function of the store
  (`steps_deterministic`), and it has no transition exactly when the machine has halted (no instruction at the
  counter), names a register it does not have, or its operation has no value (`no_step_iff`).

## Rows, and the store's invariants

A store is a bag of rows (`storeRows`): the control cell `cell ctrl 0 pc`, the flag cell `cell flag 0 w`, one
cell `cell reg key w` per register, and one instruction row `instr pc op dst src next` per counter of the table.
Words are rows through an encoding with an exact decoding (`Words`), so that an instance at 64-bit words is an
instance of every theorem here (`words64` in the module `MachineWords`, with a run and a refusal).

The invariants are properties of the bag the state reads as: **one cell per kind and key** (so one control
cell, one flag cell and one cell per register) and **one instruction row per counter**
(`Invariants` in the module `MachineInvariants`, which the rows of every store have: `storeRows_invariants`). Here they are
used in the form the proofs need: a cell row of the bag is the control cell, the flag cell or the cell of a
register of the store (`cell_of_mem_storeRows`), and the bag splits as the three rows the step takes beside the
rest (`storeRows_split`). They are part of the statement: every theorem below is at a state that reads as the
rows of a store (`Machines.ReadsBag s (storeRows words m)`), and its conclusion is again such a state, so they
are kept along every run.

## The program

Two rules with a computed condition for each operation `f` (`opRule f`, `opRuleSelf f`; `program`): take the
control cell, the destination cell and the flag cell; read the instruction row at the counter and the source
cell; let `(r, c) := f(a, b)`; make the control cell at `next`, the destination holding `r` and the flag holding
`c`. The second rule is the instruction whose source IS its destination: the source's word is the taken
cell's, and no source cell is read. One rule per set of sources that are the destination is needed and
suffices: a taken row cannot also be read, so the first rule has no evaluation on such an instruction and the
second none on any other (`opRule_apart`, `opRuleSelf_same`). Both rules are evaluable (`program_evaluable`):
the made unknowns are bound by the instruction row, the take and the operation's value.

## The theorems

* `evaluates_of_steps`, `steps_of_evaluates`: **on the rows of a store, the atomic evaluations of the program are
  the transitions of the machine**, and the evaluated bag is the rows of the next store. So the value made is
  the operation's value at the words the store holds.
* `machine_forward`, `machine_backward`: **at every state that reads as the rows of a store, an admitted firing
  of the evaluated program is a transition of the machine and its result reads as the rows of the next store;
  and every transition is an admitted firing** (identities infinitely many). The result is unique up to the made
  identities and the opening (`machine_deterministic`), and the state is stuck exactly when the machine has no
  transition (`stuck_iff`).
* `hosted`, `composite`: as `OperationalCorrespondence`s, from the machine to the atomic evaluation on bags and,
  composed with `evaluatedCorrespondence`, to the step of the evaluated program: one transition for one firing
  each way, nothing silent, the related states those that read as the rows of the store. So runs correspond in
  both directions (`runs_of_machine`, `machine_of_runs`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ComputedConditions.Machine

open Mettapedia.Logic.LP
open Mettapedia.GSLT
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis (equalityGSLT)
open NamesOnTheStep (Expr)
open LogicOverTheStep.StepSpan (Succ)
open Presentation.Schematic (Tm SRule SState X E rowSig toTerm inst Bound written isGuard equationsOf mem_vars_var
  not_mem_vars_const mem_written_of_produce)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Machines (Reads ReadsBag)

/-! ## Rows -/

/-- An unknown. -/
abbrev v (n : ℕ) : Tm := .var n

/-- A symbol. -/
abbrev k (n : ℕ) : Tm := .const (.sym n)

/-- A numeral, as a ground row. -/
abbrev e (n : ℕ) : Expr := .sym n

/-- The symbol of cells. -/
abbrev cellSym : ℕ := 1

/-- The symbol of instruction rows. -/
abbrev instrSym : ℕ := 2

/-- The symbol of the pair of an operation's two outputs. -/
abbrev pairSym : ℕ := 3

/-- The kind of the control cell. -/
abbrev ctrlKind : ℕ := 0

/-- The kind of register cells. -/
abbrev regKind : ℕ := 1

/-- The kind of the flag cell. -/
abbrev flagKind : ℕ := 2

/-- A cell: its kind, its key and its value. -/
def cell (kind key value : Tm) : Tm := spine (k cellSym) [kind, key, value]

/-- An instruction row. -/
def instr (pc op dst src next : Tm) : Tm := spine (k instrSym) [pc, op, dst, src, next]

/-- The pair of two outputs. -/
def pair (first second : Tm) : Tm := spine (k pairSym) [first, second]

/-- A ground cell. -/
def cellE (kind key value : Expr) : Expr := groundSpine (.sym cellSym) [kind, key, value]

/-- A ground instruction row. -/
def instrE (pc op dst src next : Expr) : Expr := groundSpine (.sym instrSym) [pc, op, dst, src, next]

/-- A ground pair. -/
def pairE (first second : Expr) : Expr := groundSpine (.sym pairSym) [first, second]

theorem inst_cell (θ : ℕ → Expr) (kind key value : Tm) :
    inst θ (cell kind key value) = cellE (inst θ kind) (inst θ key) (inst θ value) :=
  inst_spine θ _ _

theorem inst_instr (θ : ℕ → Expr) (pc op dst src next : Tm) :
    inst θ (instr pc op dst src next) =
      instrE (inst θ pc) (inst θ op) (inst θ dst) (inst θ src) (inst θ next) :=
  inst_spine θ _ _

theorem inst_pair (θ : ℕ → Expr) (first second : Tm) :
    inst θ (pair first second) = pairE (inst θ first) (inst θ second) :=
  inst_spine θ _ _

theorem cellE_inj {a b c a' b' c' : Expr} (same : cellE a b c = cellE a' b' c') :
    a = a' ∧ b = b' ∧ c = c' := by
  have lists := (groundSpine_inj (xs := [a, b, c]) (ys := [a', b', c']) rfl same).2
  obtain ⟨ha, rest⟩ := List.cons.inj lists
  obtain ⟨hb, rest⟩ := List.cons.inj rest
  exact ⟨ha, hb, (List.cons.inj rest).1⟩

theorem instrE_inj {p o d s n p' o' d' s' n' : Expr} (same : instrE p o d s n = instrE p' o' d' s' n') :
    p = p' ∧ o = o' ∧ d = d' ∧ s = s' ∧ n = n' := by
  have lists := (groundSpine_inj (xs := [p, o, d, s, n]) (ys := [p', o', d', s', n']) rfl same).2
  obtain ⟨hp, rest⟩ := List.cons.inj lists
  obtain ⟨ho, rest⟩ := List.cons.inj rest
  obtain ⟨hd, rest⟩ := List.cons.inj rest
  obtain ⟨hs, rest⟩ := List.cons.inj rest
  exact ⟨hp, ho, hd, hs, (List.cons.inj rest).1⟩

theorem pairE_inj {a b a' b' : Expr} (same : pairE a b = pairE a' b') : a = a' ∧ b = b' := by
  have lists := (groundSpine_inj (xs := [a, b]) (ys := [a', b']) rfl same).2
  obtain ⟨ha, rest⟩ := List.cons.inj lists
  exact ⟨ha, (List.cons.inj rest).1⟩

/-- A cell is no instruction row. -/
theorem cellE_ne_instrE {a b c p o d s n : Expr} : cellE a b c ≠ instrE p o d s n := fun same =>
  absurd (groundSpine_sym_inj same).1 (by decide)

/-- The unknowns of a cell are those of its kind, its key and its value. -/
theorem mem_vars_cell {x : ℕ} {a b c : Tm} :
    x ∈ (cell a b c).freeVars ↔ x ∈ a.freeVars ∨ x ∈ b.freeVars ∨ x ∈ c.freeVars := by
  rw [cell, mem_vars_spine]
  constructor
  · rintro (inHead | ⟨t, member, inT⟩)
    · exact absurd inHead not_mem_vars_const
    · rcases List.mem_cons.mp member with rfl | member
      · exact .inl inT
      · rcases List.mem_cons.mp member with rfl | member
        · exact .inr (.inl inT)
        · rcases List.mem_cons.mp member with rfl | member
          · exact .inr (.inr inT)
          · exact absurd member List.not_mem_nil
  · rintro (inA | inB | inC)
    · exact .inr ⟨a, List.mem_cons_self, inA⟩
    · exact .inr ⟨b, List.mem_cons_of_mem _ List.mem_cons_self, inB⟩
    · exact .inr ⟨c, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), inC⟩

/-- The unknowns of a row headed by a symbol are those of its arguments. -/
theorem mem_vars_args {x n : ℕ} {ts : List Tm} :
    x ∈ (spine (k n) ts).freeVars ↔ ∃ t ∈ ts, x ∈ t.freeVars := by
  rw [mem_vars_spine]
  constructor
  · rintro (inHead | found)
    · exact absurd inHead not_mem_vars_const
    · exact found
  · exact fun found => .inr found

/-! ## Words and operations -/

/-- **Words as rows**: an encoding of a type of machine words into ground rows, with a decoding that recovers
exactly the encoded words. -/
structure Words (W : Type) where
  enc : W → Expr
  dec : Expr → Option W
  dec_enc : ∀ w, dec (enc w) = some w
  enc_dec : ∀ {x : Expr} {w : W}, dec x = some w → enc w = x

theorem Words.enc_injective {W : Type} (words : Words W) : Function.Injective words.enc := fun a b same =>
  Option.some.inj ((words.dec_enc a).symm.trans ((congrArg words.dec same).trans (words.dec_enc b)))

variable {W : Type}

/-- **The value of an operation at two rows**: the pair of its two outputs at the words the rows encode; no
value when a row encodes no word or the operation has none. -/
def value (words : Words W) (ops : ℕ → W → W → Option (W × W)) (f : ℕ) (x y : Expr) : Option Expr :=
  (words.dec x).bind fun a => (words.dec y).bind fun b =>
    (ops f a b).map fun out => pairE (words.enc out.1) (words.enc out.2)

/-- **The interpretation of the operations** on rows: an operation takes two arguments. -/
def interp (words : Words W) (ops : ℕ → W → W → Option (W × W)) : Interpretation ℕ Expr := fun f args =>
  match args with
  | [x, y] => value words ops f x y
  | _ => none

theorem value_enc (words : Words W) (ops : ℕ → W → W → Option (W × W)) (f : ℕ) (a b : W) :
    value words ops f (words.enc a) (words.enc b) =
      (ops f a b).map fun out => pairE (words.enc out.1) (words.enc out.2) := by
  unfold value
  rw [words.dec_enc, words.dec_enc]
  rfl

/-- **A value of the interpretation is the operation's value at encoded words.** -/
theorem value_some {words : Words W} {ops : ℕ → W → W → Option (W × W)} {f : ℕ} {x y z : Expr}
    (answers : value words ops f x y = some z) :
    ∃ a b r c, words.enc a = x ∧ words.enc b = y ∧ ops f a b = some (r, c) ∧
      z = pairE (words.enc r) (words.enc c) := by
  unfold value at answers
  cases decX : words.dec x with
  | none =>
      rw [decX] at answers
      exact absurd answers (by simp)
  | some a =>
      cases decY : words.dec y with
      | none =>
          rw [decX, decY] at answers
          exact absurd answers (by simp)
      | some b =>
          rw [decX, decY] at answers
          change (ops f a b).map (fun out => pairE (words.enc out.1) (words.enc out.2)) = some z at answers
          cases out : ops f a b with
          | none =>
              rw [out] at answers
              exact absurd answers (by simp)
          | some result =>
              rw [out] at answers
              exact ⟨a, b, result.1, result.2, words.enc_dec decX, words.enc_dec decY, out,
                (Option.some.inj answers).symm⟩

/-! ## The reference machine -/

/-- **An instruction**: `(dst, flag) := op(dst, src)`, then the counter at `next`. -/
structure Instr where
  op : ℕ
  dst : ℕ
  src : ℕ
  next : ℕ

/-- **A machine store**: the counter, the flag, the registers and the instruction table. -/
structure Store (W : Type) where
  pc : ℕ
  flag : W
  regs : Finset ℕ
  reg : ℕ → W
  points : Finset ℕ
  code : ℕ → Instr

/-- **The store after the instruction at the counter**, with the operation's two outputs: the destination holds
the first, the flag the second, and the counter is at the instruction's next. -/
def after (m : Store W) (r c : W) : Store W where
  pc := (m.code m.pc).next
  flag := c
  regs := m.regs
  reg := fun key => if key = (m.code m.pc).dst then r else m.reg key
  points := m.points
  code := m.code

/-- **One transition of the reference machine.** -/
def Steps (ops : ℕ → W → W → Option (W × W)) (m m' : Store W) : Prop :=
  m.pc ∈ m.points ∧ (m.code m.pc).dst ∈ m.regs ∧ (m.code m.pc).src ∈ m.regs ∧
    ∃ r c, ops (m.code m.pc).op (m.reg (m.code m.pc).dst) (m.reg (m.code m.pc).src) = some (r, c) ∧
      m' = after m r c

/-- **The machine is a partial function of its store.** -/
theorem steps_deterministic {ops : ℕ → W → W → Option (W × W)} {m m₁ m₂ : Store W} (one : Steps ops m m₁)
    (two : Steps ops m m₂) : m₁ = m₂ := by
  obtain ⟨-, -, -, r, c, out, rfl⟩ := one
  obtain ⟨-, -, -, r', c', out', rfl⟩ := two
  have same : (r, c) = (r', c') := Option.some.inj (out.symm.trans out')
  rw [(Prod.mk.inj same).1, (Prod.mk.inj same).2]

/-- **The machine has no transition exactly when it has halted, names a register it does not have, or its
operation has no value.** -/
theorem no_step_iff (ops : ℕ → W → W → Option (W × W)) (m : Store W) :
    (¬ ∃ m', Steps ops m m') ↔ m.pc ∉ m.points ∨ (m.code m.pc).dst ∉ m.regs ∨ (m.code m.pc).src ∉ m.regs ∨
      ops (m.code m.pc).op (m.reg (m.code m.pc).dst) (m.reg (m.code m.pc).src) = none := by
  constructor
  · intro stuck
    by_cases inPoints : m.pc ∈ m.points
    · by_cases inD : (m.code m.pc).dst ∈ m.regs
      · by_cases inS : (m.code m.pc).src ∈ m.regs
        · cases out : ops (m.code m.pc).op (m.reg (m.code m.pc).dst) (m.reg (m.code m.pc).src) with
          | none => exact .inr (.inr (.inr rfl))
          | some result =>
              exact absurd ⟨after m result.1 result.2, inPoints, inD, inS, result.1, result.2, out, rfl⟩ stuck
        · exact .inr (.inr (.inl inS))
      · exact .inr (.inl inD)
    · exact .inl inPoints
  · rintro (notPoint | notD | notS | noValue) ⟨m', inPoints, inD, inS, r, c, out, -⟩
    · exact notPoint inPoints
    · exact notD inD
    · exact notS inS
    · rw [noValue] at out
      cases out

/-! ## The rows of a store -/

/-- The control cell. -/
def ctrlRow (pc : ℕ) : Expr := cellE (e ctrlKind) (e 0) (e pc)

/-- The flag cell. -/
def flagRow (w : Expr) : Expr := cellE (e flagKind) (e 0) w

/-- The cell of a register. -/
def regRow (key : ℕ) (w : Expr) : Expr := cellE (e regKind) (e key) w

/-- The row of an instruction at a counter. -/
def instrRow (p : ℕ) (i : Instr) : Expr := instrE (e p) (e i.op) (e i.dst) (e i.src) (e i.next)

/-- The cells of a set of registers. -/
def regRows (words : Words W) (m : Store W) (keys : Finset ℕ) : Multiset Expr :=
  keys.val.map fun key => regRow key (words.enc (m.reg key))

/-- The rows of the instruction table. -/
def codeRows (m : Store W) : Multiset Expr := m.points.val.map fun p => instrRow p (m.code p)

/-- **The rows of a store**: the control cell, the flag cell, one cell per register, one row per instruction. -/
def storeRows (words : Words W) (m : Store W) : Multiset Expr :=
  ({ctrlRow m.pc} : Multiset Expr) + {flagRow (words.enc m.flag)} + regRows words m m.regs + codeRows m

theorem regRows_split (words : Words W) (m : Store W) {d : ℕ} (inRegs : d ∈ m.regs) :
    regRows words m m.regs = regRow d (words.enc (m.reg d)) ::ₘ regRows words m (m.regs.erase d) := by
  unfold regRows
  rw [Finset.erase_val, ← Multiset.map_cons (fun key => regRow key (words.enc (m.reg key))),
    Multiset.cons_erase (Finset.mem_val.mpr inRegs)]

/-- **The rows of a store split** as the control cell, the cell of one register and the flag cell, beside the
other registers' cells and the instruction rows. -/
theorem storeRows_split (words : Words W) (m : Store W) {d : ℕ} (inRegs : d ∈ m.regs) :
    storeRows words m =
      (([ctrlRow m.pc, regRow d (words.enc (m.reg d)), flagRow (words.enc m.flag)] : List Expr) :
        Multiset Expr) + (regRows words m (m.regs.erase d) + codeRows m) := by
  have list : (([ctrlRow m.pc, regRow d (words.enc (m.reg d)), flagRow (words.enc m.flag)] : List Expr) :
      Multiset Expr) = {ctrlRow m.pc} + {regRow d (words.enc (m.reg d))} + {flagRow (words.enc m.flag)} := rfl
  unfold storeRows
  rw [list, regRows_split words m inRegs, ← Multiset.singleton_add]
  abel

/-- **The rows of the store after an instruction**: the control cell at the next counter, the destination
holding the first output and the flag the second, beside the other registers' cells and the instruction rows,
which are unchanged. -/
theorem storeRows_after (words : Words W) (m : Store W) (r c : W) (inRegs : (m.code m.pc).dst ∈ m.regs) :
    storeRows words (after m r c) =
      (([ctrlRow (m.code m.pc).next, regRow (m.code m.pc).dst (words.enc r), flagRow (words.enc c)] :
        List Expr) : Multiset Expr) + (regRows words m (m.regs.erase (m.code m.pc).dst) + codeRows m) := by
  have others : regRows words (after m r c) (m.regs.erase (m.code m.pc).dst) =
      regRows words m (m.regs.erase (m.code m.pc).dst) := by
    unfold regRows
    refine Multiset.map_congr rfl fun key inside => ?_
    have apart : key ≠ (m.code m.pc).dst := (Finset.mem_erase.mp (Finset.mem_val.mp inside)).1
    show regRow key (words.enc (if key = (m.code m.pc).dst then r else m.reg key)) =
      regRow key (words.enc (m.reg key))
    rw [if_neg apart]
  have own : (after m r c).reg (m.code m.pc).dst = r := if_pos rfl
  have here : storeRows words (after m r c) =
      (([ctrlRow (m.code m.pc).next, regRow (m.code m.pc).dst (words.enc ((after m r c).reg (m.code m.pc).dst)),
        flagRow (words.enc c)] : List Expr) : Multiset Expr) +
        (regRows words (after m r c) (m.regs.erase (m.code m.pc).dst) + codeRows m) :=
    storeRows_split words (after m r c) (d := (m.code m.pc).dst) inRegs
  rw [others, own] at here
  exact here

/-- **A cell row of a store is its control cell, its flag cell or the cell of one of its registers.** -/
theorem cell_of_mem_storeRows (words : Words W) (m : Store W) {kind key value : Expr}
    (inside : cellE kind key value ∈ storeRows words m) :
    (kind = e ctrlKind ∧ key = e 0 ∧ value = e m.pc) ∨
      (kind = e flagKind ∧ key = e 0 ∧ value = words.enc m.flag) ∨
      ∃ d ∈ m.regs, kind = e regKind ∧ key = e d ∧ value = words.enc (m.reg d) := by
  unfold storeRows at inside
  rcases Multiset.mem_add.mp inside with front | inCode
  · rcases Multiset.mem_add.mp front with front | inRegs
    · rcases Multiset.mem_add.mp front with isCtrl | isFlag
      · exact .inl (cellE_inj (Multiset.mem_singleton.mp isCtrl))
      · exact .inr (.inl (cellE_inj (Multiset.mem_singleton.mp isFlag)))
    · obtain ⟨d, inD, same⟩ := Multiset.mem_map.mp inRegs
      exact .inr (.inr ⟨d, Finset.mem_val.mp inD, cellE_inj same.symm⟩)
  · obtain ⟨p, -, same⟩ := Multiset.mem_map.mp inCode
    exact absurd same.symm cellE_ne_instrE

/-! ## The program -/

/-- **The rule of an operation whose source is another register than its destination**: take the control cell,
the destination cell and the flag cell; read the instruction row and the source cell; let `(r, c) := f(a, b)`;
make the control cell at the next counter, the destination holding `r` and the flag holding `c`. Unknowns: `0`
the counter, `1` the destination, `2` its word, `3` the source, `4` its word, `5` the next counter, `6` the old
flag, `7` and `8` the two outputs. -/
def opRule (f : ℕ) : RuleWithCondition ℕ Tm where
  rule := ⟨PUnit.unit, ⟨[cell (k ctrlKind) (k 0) (v 0), cell (k regKind) (v 1) (v 2), cell (k flagKind) (k 0) (v 6)],
    [instr (v 0) (k f) (v 1) (v 3) (v 5), cell (k regKind) (v 3) (v 4)], [], [],
    [cell (k ctrlKind) (k 0) (v 5), cell (k regKind) (v 1) (v 7), cell (k flagKind) (k 0) (v 8)]⟩, []⟩
  conditions := [⟨pair (v 7) (v 8), f, [v 2, v 4]⟩]

/-- **The rule of an operation whose source is its destination**: the same takes and made rows; the instruction
row names the destination twice, no source cell is read, and the operation is applied to the destination's
word twice. -/
def opRuleSelf (f : ℕ) : RuleWithCondition ℕ Tm where
  rule := ⟨PUnit.unit, ⟨[cell (k ctrlKind) (k 0) (v 0), cell (k regKind) (v 1) (v 2), cell (k flagKind) (k 0) (v 6)],
    [instr (v 0) (k f) (v 1) (v 1) (v 5)], [], [],
    [cell (k ctrlKind) (k 0) (v 5), cell (k regKind) (v 1) (v 7), cell (k flagKind) (k 0) (v 8)]⟩, []⟩
  conditions := [⟨pair (v 7) (v 8), f, [v 2, v 2]⟩]

/-- **The program**: both rules of every operation. -/
def program : Set (RuleWithCondition ℕ Tm) := {ρ | ∃ f, ρ = opRule f ∨ ρ = opRuleSelf f}

/-- The unknowns of the made rows: the next counter, the destination, and the two outputs. -/
theorem made_unknowns {t : Tm}
    (inside : t ∈ [cell (k ctrlKind) (k 0) (v 5), cell (k regKind) (v 1) (v 7), cell (k flagKind) (k 0) (v 8)])
    {x : ℕ} (vars : x ∈ t.freeVars) : x = 5 ∨ x = 1 ∨ x = 7 ∨ x = 8 := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at inside
  rcases inside with rfl | rfl | rfl
  · rcases mem_vars_cell.mp vars with inKind | inKey | inValue
    · exact absurd inKind not_mem_vars_const
    · exact absurd inKey not_mem_vars_const
    · exact .inl (mem_vars_var.mp inValue)
  · rcases mem_vars_cell.mp vars with inKind | inKey | inValue
    · exact absurd inKind not_mem_vars_const
    · exact .inr (.inl (mem_vars_var.mp inKey))
    · exact .inr (.inr (.inl (mem_vars_var.mp inValue)))
  · rcases mem_vars_cell.mp vars with inKind | inKey | inValue
    · exact absurd inKind not_mem_vars_const
    · exact absurd inKey not_mem_vars_const
    · exact .inr (.inr (.inr (mem_vars_var.mp inValue)))

theorem opRule_binds (f : ℕ) {x : ℕ} (made : x = 5 ∨ x = 1 ∨ x = 7 ∨ x = 8) : (opRule f).Binds x := by
  rcases made with rfl | rfl | rfl | rfl
  · exact .inl ⟨instr (v 0) (k f) (v 1) (v 3) (v 5), by simp [opRule],
      mem_vars_args.mpr ⟨v 5, by simp, mem_vars_var.mpr rfl⟩⟩
  · exact .inl ⟨cell (k regKind) (v 1) (v 2), by simp [opRule],
      mem_vars_cell.mpr (.inr (.inl (mem_vars_var.mpr rfl)))⟩
  · exact .inr ⟨⟨pair (v 7) (v 8), f, [v 2, v 4]⟩, by simp [opRule],
      mem_vars_args.mpr ⟨v 7, by simp, mem_vars_var.mpr rfl⟩⟩
  · exact .inr ⟨⟨pair (v 7) (v 8), f, [v 2, v 4]⟩, by simp [opRule],
      mem_vars_args.mpr ⟨v 8, by simp, mem_vars_var.mpr rfl⟩⟩

theorem opRuleSelf_binds (f : ℕ) {x : ℕ} (made : x = 5 ∨ x = 1 ∨ x = 7 ∨ x = 8) : (opRuleSelf f).Binds x := by
  rcases made with rfl | rfl | rfl | rfl
  · exact .inl ⟨instr (v 0) (k f) (v 1) (v 1) (v 5), by simp [opRuleSelf],
      mem_vars_args.mpr ⟨v 5, by simp, mem_vars_var.mpr rfl⟩⟩
  · exact .inl ⟨cell (k regKind) (v 1) (v 2), by simp [opRuleSelf],
      mem_vars_cell.mpr (.inr (.inl (mem_vars_var.mpr rfl)))⟩
  · exact .inr ⟨⟨pair (v 7) (v 8), f, [v 2, v 2]⟩, by simp [opRuleSelf],
      mem_vars_args.mpr ⟨v 7, by simp, mem_vars_var.mpr rfl⟩⟩
  · exact .inr ⟨⟨pair (v 7) (v 8), f, [v 2, v 2]⟩, by simp [opRuleSelf],
      mem_vars_args.mpr ⟨v 8, by simp, mem_vars_var.mpr rfl⟩⟩

/-- **The rule of an operation is evaluable**: its made unknowns are bound by the instruction row, the take
and the operation's value, and its arguments by the destination cell and the source cell. -/
theorem opRule_evaluable (f : ℕ) : (opRule f).Evaluable where
  noCollect := rfl
  guards := rfl
  restricted := fun t member x vars =>
    opRule_binds f (made_unknowns (by simpa [written, opRule, checkTerms] using member) vars)
  anchored := by
    intro c inside t inArguments x inT
    rw [show (opRule f).conditions = [⟨pair (v 7) (v 8), f, [v 2, v 4]⟩] from rfl, List.mem_singleton] at inside
    subst inside
    simp only [List.mem_cons, List.not_mem_nil, or_false] at inArguments
    rcases inArguments with rfl | rfl
    · rw [mem_vars_var.mp inT]
      exact .inl ⟨cell (k regKind) (v 1) (v 2), by simp [opRule],
        mem_vars_cell.mpr (.inr (.inr (mem_vars_var.mpr rfl)))⟩
    · rw [mem_vars_var.mp inT]
      exact .inl ⟨cell (k regKind) (v 3) (v 4), by simp [opRule],
        mem_vars_cell.mpr (.inr (.inr (mem_vars_var.mpr rfl)))⟩

theorem opRuleSelf_evaluable (f : ℕ) : (opRuleSelf f).Evaluable where
  noCollect := rfl
  guards := rfl
  restricted := fun t member x vars =>
    opRuleSelf_binds f (made_unknowns (by simpa [written, opRuleSelf, checkTerms] using member) vars)
  anchored := by
    intro c inside t inArguments x inT
    rw [show (opRuleSelf f).conditions = [⟨pair (v 7) (v 8), f, [v 2, v 2]⟩] from rfl, List.mem_singleton]
      at inside
    subst inside
    simp only [List.mem_cons, List.not_mem_nil, or_false] at inArguments
    rcases inArguments with rfl | rfl
    · rw [mem_vars_var.mp inT]
      exact .inl ⟨cell (k regKind) (v 1) (v 2), by simp [opRuleSelf],
        mem_vars_cell.mpr (.inr (.inr (mem_vars_var.mpr rfl)))⟩
    · rw [mem_vars_var.mp inT]
      exact .inl ⟨cell (k regKind) (v 1) (v 2), by simp [opRuleSelf],
        mem_vars_cell.mpr (.inr (.inr (mem_vars_var.mpr rfl)))⟩

/-- **Every rule of the program is evaluable.** -/
theorem program_evaluable : ∀ ρ ∈ program, ρ.Evaluable := by
  rintro ρ ⟨f, rfl | rfl⟩
  · exact opRule_evaluable f
  · exact opRuleSelf_evaluable f

/-! ## The instances of the taken and of the made rows -/

/-- The taken rows at an instantiation that reads the counter, a register with its word, and the flag. -/
theorem takes_of_reading (words : Words W) {θ : ℕ → Expr} {pc d : ℕ} {a flag : W} (θ0 : θ 0 = e pc)
    (θ1 : θ 1 = e d) (θ2 : θ 2 = words.enc a) (θ6 : θ 6 = words.enc flag) :
    [cell (k ctrlKind) (k 0) (v 0), cell (k regKind) (v 1) (v 2), cell (k flagKind) (k 0) (v 6)].map (inst θ) =
      [ctrlRow pc, regRow d (words.enc a), flagRow (words.enc flag)] := by
  rw [List.map_cons, List.map_cons, List.map_cons, List.map_nil, inst_cell, inst_cell, inst_cell]
  show [cellE (e ctrlKind) (e 0) (θ 0), cellE (e regKind) (θ 1) (θ 2), cellE (e flagKind) (e 0) (θ 6)] = _
  rw [θ0, θ1, θ2, θ6]
  rfl

/-- The made rows at an instantiation that reads the next counter, the destination and the two outputs. -/
theorem makes_of_reading (words : Words W) {θ : ℕ → Expr} {next d : ℕ} {r c : W} (θ5 : θ 5 = e next)
    (θ1 : θ 1 = e d) (θ7 : θ 7 = words.enc r) (θ8 : θ 8 = words.enc c) :
    [cell (k ctrlKind) (k 0) (v 5), cell (k regKind) (v 1) (v 7), cell (k flagKind) (k 0) (v 8)].map (inst θ) =
      [ctrlRow next, regRow d (words.enc r), flagRow (words.enc c)] := by
  rw [List.map_cons, List.map_cons, List.map_cons, List.map_nil, inst_cell, inst_cell, inst_cell]
  show [cellE (e ctrlKind) (e 0) (θ 5), cellE (e regKind) (θ 1) (θ 7), cellE (e flagKind) (e 0) (θ 8)] = _
  rw [θ5, θ1, θ7, θ8]
  rfl

/-- **The reading of a transition**: the instantiation of the rules' unknowns by the store's counter,
instruction, words and flag, and the operation's two outputs. -/
def reading (words : Words W) (m : Store W) (r c : W) : ℕ → Expr
  | 0 => e m.pc
  | 1 => e (m.code m.pc).dst
  | 2 => words.enc (m.reg (m.code m.pc).dst)
  | 3 => e (m.code m.pc).src
  | 4 => words.enc (m.reg (m.code m.pc).src)
  | 5 => e (m.code m.pc).next
  | 6 => words.enc m.flag
  | 7 => words.enc r
  | _ => words.enc c

/-! ## On the rows of a store, the atomic evaluations are the machine's transitions -/

/-- **Every transition of the machine is an atomic evaluation of a rule of the program on the rows of the
store**, and the evaluated bag is the rows of the next store. -/
theorem evaluates_of_steps (words : Words W) (ops : ℕ → W → W → Option (W × W)) {m m' : Store W}
    (steps : Steps ops m m') :
    ∃ ρ ∈ program, EvalStep (interp words ops) ρ (storeRows words m) (storeRows words m') := by
  obtain ⟨inPoints, inRegsD, inRegsS, r, c, out, rfl⟩ := steps
  have takes := congrArg (fun l : List Expr => (l : Multiset Expr) +
      (regRows words m (m.regs.erase (m.code m.pc).dst) + codeRows m))
    (takes_of_reading words (θ := reading words m r c) (pc := m.pc) (d := (m.code m.pc).dst)
      (a := m.reg (m.code m.pc).dst) (flag := m.flag) rfl rfl rfl rfl)
  have makes := congrArg (fun l : List Expr => (l : Multiset Expr) +
      (regRows words m (m.regs.erase (m.code m.pc).dst) + codeRows m))
    (makes_of_reading words (θ := reading words m r c) (next := (m.code m.pc).next)
      (d := (m.code m.pc).dst) (r := r) (c := c) rfl rfl rfl rfl)
  by_cases sameReg : (m.code m.pc).src = (m.code m.pc).dst
  · refine ⟨opRuleSelf (m.code m.pc).op, ⟨_, .inr rfl⟩, reading words m r c,
      regRows words m (m.regs.erase (m.code m.pc).dst) + codeRows m,
      takes.trans (storeRows_split words m inRegsD).symm, ?_, fun eq inside => absurd inside List.not_mem_nil,
      ?_, (storeRows_after words m r c inRegsD).trans makes.symm⟩
    · intro q inside
      have isInstr : q = instr (v 0) (k (m.code m.pc).op) (v 1) (v 1) (v 5) := by
        simpa [opRuleSelf] using inside
      have row : instrRow m.pc (m.code m.pc) = instrE (e m.pc) (e (m.code m.pc).op) (e (m.code m.pc).dst)
          (e (m.code m.pc).dst) (e (m.code m.pc).next) := by
        rw [instrRow, sameReg]
      rw [isInstr, inst_instr]
      exact Multiset.mem_add.mpr (.inr (Multiset.mem_map.mpr ⟨m.pc, Finset.mem_val.mpr inPoints, row⟩))
    · intro cond inside
      rw [show (opRuleSelf (m.code m.pc).op).conditions =
        [⟨pair (v 7) (v 8), (m.code m.pc).op, [v 2, v 2]⟩] from rfl, List.mem_singleton] at inside
      subst inside
      rw [sameReg] at out
      show value words ops (m.code m.pc).op (words.enc (m.reg (m.code m.pc).dst))
        (words.enc (m.reg (m.code m.pc).dst)) = some (inst (reading words m r c) (pair (v 7) (v 8)))
      rw [value_enc, out, inst_pair]
      rfl
  · refine ⟨opRule (m.code m.pc).op, ⟨_, .inl rfl⟩, reading words m r c,
      regRows words m (m.regs.erase (m.code m.pc).dst) + codeRows m,
      takes.trans (storeRows_split words m inRegsD).symm, ?_, fun eq inside => absurd inside List.not_mem_nil,
      ?_, (storeRows_after words m r c inRegsD).trans makes.symm⟩
    · intro q inside
      have cases : q = instr (v 0) (k (m.code m.pc).op) (v 1) (v 3) (v 5) ∨ q = cell (k regKind) (v 3) (v 4) := by
        simpa [opRule] using inside
      rcases cases with rfl | rfl
      · rw [inst_instr]
        exact Multiset.mem_add.mpr (.inr (Multiset.mem_map.mpr ⟨m.pc, Finset.mem_val.mpr inPoints, rfl⟩))
      · rw [inst_cell]
        exact Multiset.mem_add.mpr (.inl (Multiset.mem_map.mpr ⟨(m.code m.pc).src,
          Finset.mem_val.mpr (Finset.mem_erase.mpr ⟨sameReg, inRegsS⟩), rfl⟩))
    · intro cond inside
      rw [show (opRule (m.code m.pc).op).conditions =
        [⟨pair (v 7) (v 8), (m.code m.pc).op, [v 2, v 4]⟩] from rfl, List.mem_singleton] at inside
      subst inside
      show value words ops (m.code m.pc).op (words.enc (m.reg (m.code m.pc).dst))
        (words.enc (m.reg (m.code m.pc).src)) = some (inst (reading words m r c) (pair (v 7) (v 8)))
      rw [value_enc, out, inst_pair]
      rfl

/-- **The three rows the step takes are the control cell, the cell of a register and the flag cell of the
store**, and the rest is the other registers' cells and the instruction rows. -/
theorem takes_of_split (words : Words W) {m : Store W} {θ : ℕ → Expr} {rest : Multiset Expr}
    (split : (([cell (k ctrlKind) (k 0) (v 0), cell (k regKind) (v 1) (v 2), cell (k flagKind) (k 0) (v 6)].map
      (inst θ) : List Expr) : Multiset Expr) + rest = storeRows words m) :
    ∃ d ∈ m.regs, θ 0 = e m.pc ∧ θ 1 = e d ∧ θ 2 = words.enc (m.reg d) ∧ θ 6 = words.enc m.flag ∧
      rest = regRows words m (m.regs.erase d) + codeRows m := by
  have taken : [cell (k ctrlKind) (k 0) (v 0), cell (k regKind) (v 1) (v 2), cell (k flagKind) (k 0) (v 6)].map
      (inst θ) = [cellE (e ctrlKind) (e 0) (θ 0), cellE (e regKind) (θ 1) (θ 2), cellE (e flagKind) (e 0) (θ 6)] := by
    rw [List.map_cons, List.map_cons, List.map_cons, List.map_nil, inst_cell, inst_cell, inst_cell]
    rfl
  rw [taken] at split
  have inStore : ∀ x ∈ [cellE (e ctrlKind) (e 0) (θ 0), cellE (e regKind) (θ 1) (θ 2),
      cellE (e flagKind) (e 0) (θ 6)], x ∈ storeRows words m := by
    intro x inside
    rw [← split]
    exact Multiset.mem_add.mpr (.inl (Multiset.mem_coe.mpr inside))
  have θ0 : θ 0 = e m.pc := by
    rcases cell_of_mem_storeRows words m (inStore _ List.mem_cons_self) with
      ⟨-, -, value⟩ | ⟨kind, -, -⟩ | ⟨d, -, kind, -, -⟩
    · exact value
    · exact absurd (Expr.sym.inj kind) (by decide)
    · exact absurd (Expr.sym.inj kind) (by decide)
  have θ6 : θ 6 = words.enc m.flag := by
    rcases cell_of_mem_storeRows words m
        (inStore _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))) with
      ⟨kind, -, -⟩ | ⟨-, -, value⟩ | ⟨d, -, kind, -, -⟩
    · exact absurd (Expr.sym.inj kind) (by decide)
    · exact value
    · exact absurd (Expr.sym.inj kind) (by decide)
  rcases cell_of_mem_storeRows words m (inStore _ (List.mem_cons_of_mem _ List.mem_cons_self)) with
    ⟨kind, -, -⟩ | ⟨kind, -, -⟩ | ⟨d, inD, -, key, value⟩
  · exact absurd (Expr.sym.inj kind) (by decide)
  · exact absurd (Expr.sym.inj kind) (by decide)
  · refine ⟨d, inD, θ0, key, value, θ6, ?_⟩
    rw [θ0, key, value, θ6] at split
    exact add_left_cancel (split.trans (storeRows_split words m inD))

/-- **An atomic evaluation of the rule of an operation, on the rows of a store, is the machine's transition**,
at an instruction of that operation whose source is another register than its destination; the evaluated bag is
the rows of the next store. -/
theorem opRule_steps (words : Words W) (ops : ℕ → W → W → Option (W × W)) {m : Store W} {f : ℕ}
    {B' : Multiset Expr} (evaluates : EvalStep (interp words ops) (opRule f) (storeRows words m) B') :
    (m.code m.pc).src ≠ (m.code m.pc).dst ∧ ∃ m', Steps ops m m' ∧ B' = storeRows words m' := by
  obtain ⟨θ, rest, split, reads, -, conditions, rfl⟩ := evaluates
  obtain ⟨d, inD, θ0, θ1, θ2, θ6, restEq⟩ := takes_of_split words split
  -- the instruction row read is the store's instruction at its counter
  have inRest := reads (instr (v 0) (k f) (v 1) (v 3) (v 5)) (by simp [opRule])
  rw [inst_instr, restEq] at inRest
  rcases Multiset.mem_add.mp inRest with inRegs | inCode
  · obtain ⟨key, -, same⟩ := Multiset.mem_map.mp inRegs
    exact absurd same cellE_ne_instrE
  obtain ⟨p, inP, same⟩ := Multiset.mem_map.mp inCode
  obtain ⟨hp, ho, hd, hs, hn⟩ := instrE_inj same
  have pEq : p = m.pc := Expr.sym.inj (hp.trans θ0)
  subst pEq
  have opEq : (m.code m.pc).op = f := Expr.sym.inj ho
  have dEq : (m.code m.pc).dst = d := Expr.sym.inj (hd.trans θ1)
  subst dEq
  -- the source cell read is the cell of the instruction's source, another register than the destination
  have inRest' := reads (cell (k regKind) (v 3) (v 4)) (by simp [opRule])
  rw [inst_cell, restEq] at inRest'
  rcases Multiset.mem_add.mp inRest' with inRegs | inCode'
  swap
  · obtain ⟨q, -, same'⟩ := Multiset.mem_map.mp inCode'
    exact absurd same'.symm cellE_ne_instrE
  obtain ⟨key, inErase, same'⟩ := Multiset.mem_map.mp inRegs
  obtain ⟨-, hkey, hvalue⟩ := cellE_inj same'
  have keyEq : key = (m.code m.pc).src := Expr.sym.inj (hkey.trans hs.symm)
  subst keyEq
  obtain ⟨apart, inS⟩ := Finset.mem_erase.mp (Finset.mem_val.mp inErase)
  -- the operation's value at the words the two registers hold
  have valued : value words ops f (θ 2) (θ 4) = some (pairE (θ 7) (θ 8)) :=
    (conditions ⟨pair (v 7) (v 8), f, [v 2, v 4]⟩ (by simp [opRule])).trans
      (congrArg some (inst_pair θ (v 7) (v 8)))
  obtain ⟨a, b, r, c, encA, encB, out, outputs⟩ := value_some valued
  obtain ⟨θ7, θ8⟩ := pairE_inj outputs
  have aEq : a = m.reg (m.code m.pc).dst := words.enc_injective (encA.trans θ2)
  have bEq : b = m.reg (m.code m.pc).src := words.enc_injective (encB.trans hvalue.symm)
  subst aEq bEq opEq
  refine ⟨apart, after m r c, ⟨Finset.mem_val.mp inP, inD, inS, r, c, out, rfl⟩, ?_⟩
  have makes := congrArg (fun l : List Expr => (l : Multiset Expr) +
      (regRows words m (m.regs.erase (m.code m.pc).dst) + codeRows m))
    (makes_of_reading words (θ := θ) (next := (m.code m.pc).next) (d := (m.code m.pc).dst) (r := r) (c := c)
      hn.symm θ1 θ7 θ8)
  rw [restEq]
  exact makes.trans (storeRows_after words m r c inD).symm

/-- **An atomic evaluation of the rule for a source that is the destination, on the rows of a store, is the
machine's transition**, at an instruction of that operation whose source is its destination. -/
theorem opRuleSelf_steps (words : Words W) (ops : ℕ → W → W → Option (W × W)) {m : Store W} {f : ℕ}
    {B' : Multiset Expr} (evaluates : EvalStep (interp words ops) (opRuleSelf f) (storeRows words m) B') :
    (m.code m.pc).src = (m.code m.pc).dst ∧ ∃ m', Steps ops m m' ∧ B' = storeRows words m' := by
  obtain ⟨θ, rest, split, reads, -, conditions, rfl⟩ := evaluates
  obtain ⟨d, inD, θ0, θ1, θ2, θ6, restEq⟩ := takes_of_split words split
  have inRest := reads (instr (v 0) (k f) (v 1) (v 1) (v 5)) (by simp [opRuleSelf])
  rw [inst_instr, restEq] at inRest
  rcases Multiset.mem_add.mp inRest with inRegs | inCode
  · obtain ⟨key, -, same⟩ := Multiset.mem_map.mp inRegs
    exact absurd same cellE_ne_instrE
  obtain ⟨p, inP, same⟩ := Multiset.mem_map.mp inCode
  obtain ⟨hp, ho, hd, hs, hn⟩ := instrE_inj same
  have pEq : p = m.pc := Expr.sym.inj (hp.trans θ0)
  subst pEq
  have opEq : (m.code m.pc).op = f := Expr.sym.inj ho
  have dEq : (m.code m.pc).dst = d := Expr.sym.inj (hd.trans θ1)
  subst dEq
  have sameReg : (m.code m.pc).src = (m.code m.pc).dst := Expr.sym.inj (hs.trans hd.symm)
  have inS : (m.code m.pc).src ∈ m.regs := by
    rw [sameReg]
    exact inD
  have valued : value words ops f (θ 2) (θ 2) = some (pairE (θ 7) (θ 8)) :=
    (conditions ⟨pair (v 7) (v 8), f, [v 2, v 2]⟩ (by simp [opRuleSelf])).trans
      (congrArg some (inst_pair θ (v 7) (v 8)))
  obtain ⟨a, b, r, c, encA, encB, out, outputs⟩ := value_some valued
  obtain ⟨θ7, θ8⟩ := pairE_inj outputs
  have aEq : a = m.reg (m.code m.pc).dst := words.enc_injective (encA.trans θ2)
  have bEq : b = m.reg (m.code m.pc).src := by
    rw [sameReg]
    exact words.enc_injective (encB.trans θ2)
  subst aEq bEq opEq
  refine ⟨sameReg, after m r c, ⟨Finset.mem_val.mp inP, inD, inS, r, c, out, rfl⟩, ?_⟩
  have makes := congrArg (fun l : List Expr => (l : Multiset Expr) +
      (regRows words m (m.regs.erase (m.code m.pc).dst) + codeRows m))
    (makes_of_reading words (θ := θ) (next := (m.code m.pc).next) (d := (m.code m.pc).dst) (r := r) (c := c)
      hn.symm θ1 θ7 θ8)
  rw [restEq]
  exact makes.trans (storeRows_after words m r c inD).symm

/-- **On the rows of a store, an atomic evaluation of a rule of the program is the machine's transition**, and
the evaluated bag is the rows of the next store. -/
theorem steps_of_evaluates (words : Words W) (ops : ℕ → W → W → Option (W × W)) {m : Store W}
    {ρ : RuleWithCondition ℕ Tm} (member : ρ ∈ program) {B' : Multiset Expr}
    (evaluates : EvalStep (interp words ops) ρ (storeRows words m) B') :
    ∃ m', Steps ops m m' ∧ B' = storeRows words m' := by
  obtain ⟨f, rfl | rfl⟩ := member
  · exact (opRule_steps words ops evaluates).2
  · exact (opRuleSelf_steps words ops evaluates).2

/-- **The rule that reads the source cell has no evaluation on an instruction whose source is its
destination**: the destination cell is taken, and a taken row is not read. -/
theorem opRule_apart (words : Words W) (ops : ℕ → W → W → Option (W × W)) {m : Store W} {f : ℕ}
    (sameReg : (m.code m.pc).src = (m.code m.pc).dst) (B' : Multiset Expr) :
    ¬ EvalStep (interp words ops) (opRule f) (storeRows words m) B' := fun evaluates =>
  (opRule_steps words ops evaluates).1 sameReg

/-- **The rule for a source that is the destination has no evaluation on any other instruction.** -/
theorem opRuleSelf_same (words : Words W) (ops : ℕ → W → W → Option (W × W)) {m : Store W} {f : ℕ}
    (apart : (m.code m.pc).src ≠ (m.code m.pc).dst) (B' : Multiset Expr) :
    ¬ EvalStep (interp words ops) (opRuleSelf f) (storeRows words m) B' := fun evaluates =>
  apart (opRuleSelf_steps words ops evaluates).1

/-! ## At every state that reads as the rows of a store -/

section States

variable {O : Type} [DecidableEq O]

/-- **An admitted firing of the evaluated program, at a state that reads as the rows of a store, is a transition
of the machine, and its result reads as the rows of the next store.** So the value made is the operation's value
at the words the store holds. -/
theorem machine_backward (words : Words W) (ops : ℕ → W → W → Option (W × W)) {s : SState O} {m : Store W}
    (reads : ReadsBag s (storeRows words m)) (f : Firing O E (evaluated (interp words ops) program) s.frame)
    (admitted : (step X O E (evaluated (interp words ops) program)).Admits (s := s) f) :
    ∃ m', Steps ops m m' ∧ ReadsBag (f.result X s) (storeRows words m') := by
  obtain ⟨bag', ⟨ρ, member, evaluates⟩, reads'⟩ := evaluated_backward
    (fun ρ inP t inProduce x vars =>
      (program_evaluable ρ inP).restricted t (mem_written_of_produce inProduce) x vars) reads f admitted
  obtain ⟨m', steps, rfl⟩ := steps_of_evaluates words ops member evaluates
  exact ⟨m', steps, reads'⟩

/-- **Every transition of the machine is an admitted firing of the evaluated program, at every state that reads
as the rows of the store, and its result reads as the rows of the next store**, when identities are infinitely
many. -/
theorem machine_forward [Infinite O] (words : Words W) (ops : ℕ → W → W → Option (W × W)) {s : SState O}
    {m m' : Store W} (reads : ReadsBag s (storeRows words m)) (steps : Steps ops m m') :
    ∃ (f : Firing O E (evaluated (interp words ops) program) s.frame)
      (_ : (step X O E (evaluated (interp words ops) program)).Admits (s := s) f),
      ReadsBag (f.result X s) (storeRows words m') := by
  obtain ⟨ρ, member, evaluates⟩ := evaluates_of_steps words ops steps
  exact evaluated_forward program_evaluable reads member evaluates

/-- **The result of a firing is determined up to the made identities and the opening**: two admitted firings at
a state that reads as the rows of a store have results that read as the rows of one and the same store. -/
theorem machine_deterministic (words : Words W) (ops : ℕ → W → W → Option (W × W)) {s : SState O}
    {m : Store W} (reads : ReadsBag s (storeRows words m))
    (f g : Firing O E (evaluated (interp words ops) program) s.frame)
    (admitted : (step X O E (evaluated (interp words ops) program)).Admits (s := s) f)
    (admitted' : (step X O E (evaluated (interp words ops) program)).Admits (s := s) g) :
    ∃ m', ReadsBag (f.result X s) (storeRows words m') ∧ ReadsBag (g.result X s) (storeRows words m') := by
  obtain ⟨m₁, one, reads₁⟩ := machine_backward words ops reads f admitted
  obtain ⟨m₂, two, reads₂⟩ := machine_backward words ops reads g admitted'
  have same := steps_deterministic one two
  subst same
  exact ⟨m₁, reads₁, reads₂⟩

/-- **A state that reads as the rows of a store is stuck exactly when the machine has no transition**: it has
halted, names a register it does not have, or its operation has no value (`no_step_iff`). -/
theorem stuck_iff [Infinite O] (words : Words W) (ops : ℕ → W → W → Option (W × W)) {s : SState O}
    {m : Store W} (reads : ReadsBag s (storeRows words m)) :
    (¬ ∃ f : Firing O E (evaluated (interp words ops) program) s.frame,
      (step X O E (evaluated (interp words ops) program)).Admits (s := s) f) ↔ ¬ ∃ m', Steps ops m m' := by
  constructor
  · rintro stuck ⟨m', steps⟩
    obtain ⟨f, admitted, -⟩ := machine_forward words ops reads steps
    exact stuck ⟨f, admitted⟩
  · rintro halted ⟨f, admitted⟩
    obtain ⟨m', steps, -⟩ := machine_backward words ops reads f admitted
    exact halted ⟨m', steps⟩

/-! ## The correspondences -/

/-- **The reference machine, as a system**: stores, equal when identical, under its transition. -/
def machineSystem (ops : ℕ → W → W → Option (W × W)) : GSLT := equalityGSLT (Store W) (Steps ops)

/-- **The machine and the atomic evaluation of the program on bags**: one transition for one evaluation, both
ways, related when the bag is the rows of the store. -/
def hosted (words : Words W) (ops : ℕ → W → W → Option (W × W)) :
    OperationalCorrespondence (machineSystem ops) (evaluation (interp words ops) program) where
  related m bag := bag = storeRows words m
  readStep := by
    rintro m bag bag' rfl ⟨ρ, member, evaluates⟩
    obtain ⟨m', steps, rfl⟩ := steps_of_evaluates words ops member evaluates
    exact Or.inr ⟨m', steps, rfl⟩
  forward := by
    rintro m m' bag rfl steps
    exact ⟨storeRows words m',
      (executionPath_nonempty_iff_multiStep (evaluation (interp words ops) program) _ _).mpr
        (.step (evaluates_of_steps words ops steps) (.refl _)), rfl⟩

/-- **The machine and the step of the evaluated program**: the composite of `hosted` with the correspondence
between the atomic evaluation on bags and the step. One transition for one firing each way, no firing silent;
a store is related to the states that read as its rows. -/
def composite [Infinite O] (words : Words W) (ops : ℕ → W → W → Option (W × W)) :
    OperationalCorrespondence (machineSystem ops) (programSystem O (evaluated (interp words ops) program)) :=
  (hosted words ops).comp (evaluatedCorrespondence program_evaluable)

/-- **Every run of the machine is a run of the evaluated program**, from every state that reads as the rows of
the store, to a state that reads as the rows of the run's last store. -/
theorem runs_of_machine [Infinite O] (words : Words W) (ops : ℕ → W → W → Option (W × W)) {s : SState O}
    {m m' : Store W} (reads : ReadsBag s (storeRows words m)) (run : (machineSystem ops).MultiStep m m') :
    ∃ s', (programSystem O (evaluated (interp words ops) program)).MultiStep s s' ∧
      ReadsBag s' (storeRows words m') := by
  obtain ⟨s', path, bag, same, reads'⟩ := (composite (O := O) words ops).liftMultiStep
    (show ∃ bag, bag = storeRows words m ∧ ReadsBag s bag from ⟨_, rfl, reads⟩) run
  have sameBag : bag = storeRows words m' := same
  subst sameBag
  exact ⟨s', path, reads'⟩

/-- **Every run of the evaluated program, from a state that reads as the rows of a store, is a run of the
machine**, and its last state reads as the rows of the machine's last store. -/
theorem machine_of_runs [Infinite O] (words : Words W) (ops : ℕ → W → W → Option (W × W)) {s s' : SState O}
    {m : Store W} (reads : ReadsBag s (storeRows words m))
    (run : (programSystem O (evaluated (interp words ops) program)).MultiStep s s') :
    ∃ m', (machineSystem ops).MultiStep m m' ∧ ReadsBag s' (storeRows words m') := by
  obtain ⟨m', path, bag, same, reads'⟩ :=
    (composite (O := O) words ops).toOperationalReadback.reflectMultiStep
      (show ∃ bag, bag = storeRows words m ∧ ReadsBag s bag from ⟨_, rfl, reads⟩) run
  have sameBag : bag = storeRows words m' := same
  subst sameBag
  exact ⟨m', path, reads'⟩

end States

/-- **Every store is read from a state**, so the theorems at every state that reads as the rows of a store are
about something. -/
theorem exists_state (words : Words W) (m : Store W) : ∃ s : SState ℕ, ReadsBag s (storeRows words m) :=
  Machines.exists_reads _

#print axioms takes_of_split
#print axioms opRule_steps
#print axioms opRuleSelf_steps
#print axioms steps_of_evaluates
#print axioms machine_backward
#print axioms machine_forward
#print axioms machine_deterministic
#print axioms stuck_iff
#print axioms hosted
#print axioms composite
#print axioms runs_of_machine
#print axioms machine_of_runs
#print axioms value_some
#print axioms steps_deterministic
#print axioms no_step_iff
#print axioms storeRows_split
#print axioms storeRows_after
#print axioms cell_of_mem_storeRows
#print axioms program_evaluable
#print axioms evaluates_of_steps

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ComputedConditions.Machine
