import Mathlib.Data.Finset.Basic
import Mathlib.Logic.Function.Basic

/-!
# Lowering equation bodies to register code

A runtime evaluates a pure equation body in one of two ways.  The *node executor* walks the
body's tree.  The *register code* is the body lowered to instructions over the activation's
registers: the body's locals first, then one temporary for each value computed on the way.
This module models both over abstract values, literals, operations, let patterns and heads,
every primitive step partial (`none` is the machine declining), and gives the lowering as the
runtime performs it: a literal or a local is read in place, any other operand is computed into
a fresh temporary, operands left to right, an operation in tail position answers directly, and a
condition that is a chosen operation (`fuses`) is fused with its branch.  It proves:

- **Lowering preserves meaning** (`lower_lands`, `lower_answers`).  Lowered into a register, the
  code declines exactly when the node executor does, and otherwise falls through with the value
  in that register and the locals agreeing.  Lowered in tail position, it declines exactly when
  the node executor does, and otherwise answers the same value.  With fuel, spent only at calls:
  `lower_sound`, `lower_complete`, `lower_ne_ret`, `lower_none_iff`, `lower_tail_ret_iff`,
  `lower_tail_ne_next`, `lower_tail_none_iff`.
- **An answer producer's steps** (`lower_step_answers`, `lower_step_slots`,
  `lower_step_answers_fuel`): a step's region, lowered into a register of its own above the
  frame's slots and returned (`stepCode`), declines exactly when the node executor does, and
  otherwise answers its value and leaves the frame's slots as the node executor does.
- **Calls are answered alike** (`codeAnswer_eq_nodeAnswer`): for every fuel, the register
  machine answers every call as the node executor does, whatever each activation's registers
  hold outside the locals its head match binds.
- **Dead registers do not matter** (`exec_live`): register files agreeing on the live-in of a
  piece of code, as a backward pass computes it, give the same outcome.  So a collector may
  clear every register the rest of the body does not read once a call has read its arguments
  (`call_collect`); before that it must keep the arguments too (`call_trim`, `tailCall_trim`);
  when the call returns, it must keep the register its answer was written to (`call_resume`).
- **Fusing a condition with its branch** (`iteOp_fuse`), **answering an operation directly**
  (`opRet_eq`) and **a tail call** (`tailCall_eq`) change nothing.

The hypotheses are the runtime's compile-time discipline.  A body is *scoped* (`Scoped`): it
reads only locals bound at that point, and each let compares only against locals in scope and
binds fresh ones, never a local already in scope.  The lowering needs this: an operand that
reads a local is read when the instruction consuming it runs, after the later operands, so a
later let rebinding that local would change the value (`Example.rebindingLet`).  A let's match
may depend only on the value and the locals it compares against (`Sem.bindLet_local`).

Not modeled: branches flattened into jumps, the encoding of operands and literals, the root
program's entry arguments, the limits at which the runtime declines to lower a body, the unboxed
shortcut of a fused comparison (taken to compute the operation's truth), and the collector's
walk over all activations (each activation owns its registers, so the per-call results apply
to each).
-/

set_option autoImplicit false

namespace Mettapedia.Machines.RegisterCode

/-! ## Bodies and the machine's primitive steps -/

/-- A register file: register `i` holds `R i`, or nothing. -/
abbrev Regs (V : Type) := Nat → Option V

/-- An equation body as the node executor evaluates it. -/
inductive Node (L O P H : Type) where
  /-- A literal. -/
  | lit : L → Node L O P H
  /-- Read local `i`. -/
  | slot : Nat → Node L O P H
  /-- An operation (constructor, arithmetic, intrinsic or observation) on the children's
  values. -/
  | op : O → List (Node L O P H) → Node L O P H
  /-- A conditional. -/
  | ite : Node L O P H → Node L O P H → Node L O P H → Node L O P H
  /-- Match the value against a let pattern, binding its locals, then the body. -/
  | bind : Node L O P H → P → Node L O P H → Node L O P H
  /-- Call a head on the children's values. -/
  | call : H → List (Node L O P H) → Node L O P H

/-- What lowering and liveness know of a let pattern: the locals it compares against, which are
bound before it, and the locals it binds. -/
structure Patterns (P : Type) where
  patReads : P → List Nat
  patSlots : P → List Nat

/-- An equation entered by a call: its body, its number of locals (the registers below it; the
body's temporaries lie above), the locals its head match binds, and their values. -/
structure Entered (V L O P H : Type) where
  body : Node L O P H
  locals : Nat
  bound : Finset Nat
  regs : Regs V

/-- The machine's primitive steps, each partial: `none` is a decline. -/
structure Sem (V L O P H : Type) extends Patterns P where
  lit : L → V
  op : O → List V → Option V
  /-- Which branch a value selects; `none` when it is not a condition. -/
  truth : V → Option Bool
  /-- Match a value against a let pattern, writing the locals it binds. -/
  bindLet : P → V → Regs V → Option (Regs V)
  /-- A let match changes only the locals its pattern binds. -/
  bindLet_frame : ∀ {p v R R'}, bindLet p v R = some R' → ∀ i ∉ patSlots p, R' i = R i
  /-- Whether a let matches, and what it binds, depend only on the locals it compares
  against. -/
  bindLet_local : ∀ {p v R₁ R₂}, (∀ i ∈ patReads p, R₁ i = R₂ i) →
    Option.Rel (fun R₁' R₂' => ∀ i ∈ patSlots p, R₁' i = R₂' i)
      (bindLet p v R₁) (bindLet p v R₂)
  /-- Equation selection and head match. -/
  enter : H → List V → Option (Entered V L O P H)

variable {V L O P H : Type}

/-! ## The node executor -/

section NodeExecutor
variable (S : Sem V L O P H) (ans : H → List V → Option V)

mutual
/-- The node executor on one body, its calls answered by `ans`: the value, and the registers
after it (a let's writes stay in them). -/
def eval : Regs V → Node L O P H → Option (V × Regs V)
  | N, .lit l => some (S.lit l, N)
  | N, .slot i => (N i).map fun v => (v, N)
  | N, .op o cs => (evalList N cs).bind fun r => (S.op o r.1).map fun v => (v, r.2)
  | N, .ite c t e => (eval N c).bind fun r => (S.truth r.1).bind fun b =>
      if b then eval r.2 t else eval r.2 e
  | N, .bind c p b => (eval N c).bind fun r => (S.bindLet p r.1 r.2).bind fun N' => eval N' b
  | N, .call h cs => (evalList N cs).bind fun r => (ans h r.1).map fun v => (v, r.2)
/-- Children, left to right. -/
def evalList : Regs V → List (Node L O P H) → Option (List V × Regs V)
  | N, [] => some ([], N)
  | N, c :: cs => (eval N c).bind fun r =>
      (evalList r.2 cs).map fun rs => (r.1 :: rs.1, rs.2)
end

end NodeExecutor

/-- The node executor's answer to a call with fuel `n`; fuel is spent only at calls, and the
callee's body runs in the registers its entry binds.  With these answers, `eval` is the node
executor with fuel `n`. -/
def nodeAnswer (S : Sem V L O P H) : Nat → H → List V → Option V
  | 0, _, _ => none
  | n + 1, h, vs => (S.enter h vs).bind fun e =>
      (eval S (nodeAnswer S n) e.regs e.body).map Prod.fst

/-! ## Register code -/

/-- An operand: a register, or a literal. -/
inductive Operand (L : Type) where
  | reg : Nat → Operand L
  | lit : L → Operand L

/-- Register code with structured control; the runtime flattens `ite` and `iteOp` into a
branch and a jump. -/
inductive Instr (L O P H : Type) where
  /-- `dst ← src` -/
  | move (dst : Nat) (src : Operand L)
  /-- `dst ← o args` -/
  | op (dst : Nat) (o : O) (args : List (Operand L))
  /-- `o args` answers for the body, writing no register. -/
  | opRet (o : O) (args : List (Operand L))
  /-- Branch on the value of `cond`. -/
  | ite (cond : Operand L) (thenCode elseCode : List (Instr L O P H))
  /-- Branch on the value of `o args`, writing no register. -/
  | iteOp (o : O) (args : List (Operand L)) (thenCode elseCode : List (Instr L O P H))
  /-- Match `src` against let pattern `p`, binding its locals. -/
  | bind (src : Operand L) (p : P)
  /-- `dst ← h args` -/
  | call (dst : Nat) (h : H) (args : List (Operand L))
  /-- `h args` answers for the body. -/
  | tailCall (h : H) (args : List (Operand L))
  /-- `src` answers for the body. -/
  | ret (src : Operand L)

/-- How code ends: it fell through with registers `R`, or the body answered `v`. -/
inductive Outcome (V : Type) where
  | next (R : Regs V)
  | ret (v : V)

/-- Continue with `k` from code that fell through; an answer ends the body. -/
def andThen : Option (Outcome V) → (Regs V → Option (Outcome V)) → Option (Outcome V)
  | none, _ => none
  | some (.next R), k => k R
  | some (.ret v), _ => some (.ret v)

/-- A body's answer: its `ret`.  A body that declines or falls through answers nothing. -/
def answer : Option (Outcome V) → Option V
  | some (.ret v) => some v
  | _ => none

section RegisterExecutor
variable (S : Sem V L O P H) (ans : H → List V → Option V)

/-- An operand's value; an unset register reads nothing. -/
def read (R : Regs V) : Operand L → Option V
  | .reg i => R i
  | .lit l => some (S.lit l)

/-- Operand values, left to right. -/
def readAll (R : Regs V) : List (Operand L) → Option (List V)
  | [] => some []
  | a :: as => (read S R a).bind fun v => (readAll R as).map (v :: ·)

mutual
/-- One instruction, its calls answered by `ans`. -/
def step : Instr L O P H → Regs V → Option (Outcome V)
  | .move dst src, R => (read S R src).map fun v => .next (Function.update R dst (some v))
  | .op dst o args, R => (readAll S R args).bind fun vs =>
      (S.op o vs).map fun v => .next (Function.update R dst (some v))
  | .opRet o args, R => (readAll S R args).bind fun vs => (S.op o vs).map .ret
  | .ite a t e, R => (read S R a).bind fun v => (S.truth v).bind fun b =>
      if b then exec t R else exec e R
  | .iteOp o args t e, R => (readAll S R args).bind fun vs => (S.op o vs).bind fun v =>
      (S.truth v).bind fun b => if b then exec t R else exec e R
  | .bind src p, R => (read S R src).bind fun v => (S.bindLet p v R).map .next
  | .call dst h args, R => (readAll S R args).bind fun vs =>
      (ans h vs).map fun v => .next (Function.update R dst (some v))
  | .tailCall h args, R => (readAll S R args).bind fun vs => (ans h vs).map .ret
  | .ret src, R => (read S R src).map .ret
/-- A sequence of instructions. -/
def exec : List (Instr L O P H) → Regs V → Option (Outcome V)
  | [], R => some (.next R)
  | i :: rest, R => andThen (step i R) (exec rest)
end

end RegisterExecutor

/-! ## Lowering -/

section Lowering
variable (fuses : O → Nat → Bool)

/-- The operand standing for `e`'s value, given `low`, the lowering of `e` into register
`next`: a literal or a local is read where it is, and any other node is computed into `next`
first.  Returns the code, the operand, and the next free register. -/
def operand (e : Node L O P H) (next : Nat) (low : List (Instr L O P H) × Nat) :
    List (Instr L O P H) × Operand L × Nat :=
  match e with
  | .lit l => ([], .lit l, next)
  | .slot i => ([], .reg i, next)
  | _ => (low.1, .reg next, low.2)

mutual
/-- Lower a node: in tail position (`tail`) its code answers for the body, otherwise it puts the
value in `dst`.  Registers from `next` up are free; returns the code and the next free register.
Operands are computed left to right, a condition before its branch and a bound value before its
pattern.  In tail position an operation answers directly (`opRet`), taking no register.  A
condition that is an operation `o` on `k` operands with `fuses o k` is fused with its branch
(`iteOp`). -/
def compile : Node L O P H → Bool → Nat → Nat → List (Instr L O P H) × Nat
  | .lit l, tail, dst, next =>
      (if tail then [.ret (.lit l)] else [.move dst (.lit l)], next)
  | .slot i, tail, dst, next =>
      (if tail then [.ret (.reg i)] else [.move dst (.reg i)], next)
  | .op o cs, tail, dst, next =>
      let a := compileArgs cs next
      (a.1 ++ [if tail then .opRet o a.2.1 else .op dst o a.2.1], a.2.2)
  | .ite (.op o cs) t e, tail, dst, next =>
      if fuses o cs.length then
        let a := compileArgs cs next
        let tc := compile t tail dst a.2.2
        let ec := compile e tail dst tc.2
        (a.1 ++ [.iteOp o a.2.1 tc.1 ec.1], ec.2)
      else
        let c := compile (.op o cs) false next (next + 1)
        let tc := compile t tail dst c.2
        let ec := compile e tail dst tc.2
        (c.1 ++ [.ite (.reg next) tc.1 ec.1], ec.2)
  | .ite c t e, tail, dst, next =>
      let a := operand c next (compile c false next (next + 1))
      let tc := compile t tail dst a.2.2
      let ec := compile e tail dst tc.2
      (a.1 ++ [.ite a.2.1 tc.1 ec.1], ec.2)
  | .bind c p b, tail, dst, next =>
      let a := operand c next (compile c false next (next + 1))
      let bc := compile b tail dst a.2.2
      (a.1 ++ .bind a.2.1 p :: bc.1, bc.2)
  | .call h cs, tail, dst, next =>
      let a := compileArgs cs next
      (a.1 ++ [if tail then .tailCall h a.2.1 else .call dst h a.2.1], a.2.2)
/-- Lower children to operands, left to right: the code, the operands, the next free
register. -/
def compileArgs : List (Node L O P H) → Nat →
    List (Instr L O P H) × List (Operand L) × Nat
  | [], next => ([], [], next)
  | c :: cs, next =>
      let a := operand c next (compile c false next (next + 1))
      let r := compileArgs cs a.2.2
      (a.1 ++ r.1, a.2.1 :: r.2.1, r.2.2)
end

/-- The code of an answer producer's step over a frame of `m` slots.  A tail call reuses its
activation's registers, and a step does not own the frame's slots: the search reads them after
the step.  So a step never ends in a tail call; its region is lowered, not in tail position, into
register `m`, a register of its own above the slots, and that register is returned. -/
def stepCode (e : Node L O P H) (m : Nat) : List (Instr L O P H) :=
  (compile fuses e false m (m + 1)).1 ++ [.ret (.reg m)]

end Lowering

/-- A callee's registers: the locals its head match binds, and `junk` everywhere else. -/
def Entered.fill (e : Entered V L O P H) (junk : Regs V) : Regs V :=
  fun i => if i ∈ e.bound then e.regs i else junk i

/-- The register machine's answer to a call with fuel `n`: the callee's body, lowered in tail
position with its temporaries from its local count up, runs in registers holding its bound
locals and `junk n h vs` in every other register. -/
def codeAnswer (S : Sem V L O P H) (fuses : O → Nat → Bool)
    (junk : Nat → H → List V → Regs V) : Nat → H → List V → Option V
  | 0, _, _ => none
  | n + 1, h, vs => (S.enter h vs).bind fun e =>
      answer (exec S (codeAnswer S fuses junk n) (compile fuses e.body true 0 e.locals).1
        (e.fill (junk n h vs)))

/-! ## Scope -/

section Scope
variable (π : Patterns P) (m : Nat)

mutual
/-- `e` reads only locals in scope `Γ`, and each let in it compares only against locals in
scope and binds locals below `m` that are not yet in scope; they are in scope in its body. -/
def Scoped : Finset Nat → Node L O P H → Prop
  | _, .lit _ => True
  | Γ, .slot i => i ∈ Γ
  | Γ, .op _ cs => ScopedArgs Γ cs
  | Γ, .ite c t e => Scoped Γ c ∧ Scoped Γ t ∧ Scoped Γ e
  | Γ, .bind c p b => Scoped Γ c ∧ (∀ i ∈ π.patReads p, i ∈ Γ) ∧
      (∀ i ∈ π.patSlots p, i < m ∧ i ∉ Γ) ∧ Scoped (Γ ∪ (π.patSlots p).toFinset) b
  | Γ, .call _ cs => ScopedArgs Γ cs
/-- Every child is scoped. -/
def ScopedArgs : Finset Nat → List (Node L O P H) → Prop
  | _, [] => True
  | Γ, c :: cs => Scoped Γ c ∧ ScopedArgs Γ cs
end

end Scope

/-- Every equation `enter` selects binds locals below its local count, and its body is scoped
from them. -/
def EntersScoped (S : Sem V L O P H) : Prop :=
  ∀ h vs e, S.enter h vs = some e →
    (∀ i ∈ e.bound, i < e.locals) ∧ Scoped S.toPatterns e.locals e.bound e.body

/-! ## Liveness -/

/-- The register an operand reads. -/
def Operand.regs : Operand L → Finset Nat
  | .reg i => {i}
  | .lit _ => ∅

/-- The registers operands read. -/
def operandRegs : List (Operand L) → Finset Nat
  | [] => ∅
  | a :: as => a.regs ∪ operandRegs as

section Liveness
variable (π : Patterns P)

mutual
/-- Live-in of an instruction from its live-out, as a backward pass computes it: an
instruction reads its register operands and a let pattern also the locals it compares against;
it kills the register it writes, and a let pattern the locals it binds; a branch joins its
arms; `ret`, `opRet` and `tailCall` end the body. -/
def liveStep : Instr L O P H → Finset Nat → Finset Nat
  | .move dst src, out => out.erase dst ∪ src.regs
  | .op dst _ args, out => out.erase dst ∪ operandRegs args
  | .opRet _ args, _ => operandRegs args
  | .ite a t e, out => liveIn t out ∪ liveIn e out ∪ a.regs
  | .iteOp _ args t e, out => liveIn t out ∪ liveIn e out ∪ operandRegs args
  | .bind src p, out =>
      out \ (π.patSlots p).toFinset ∪ (π.patReads p).toFinset ∪ src.regs
  | .call dst _ args, out => out.erase dst ∪ operandRegs args
  | .tailCall _ args, _ => operandRegs args
  | .ret src, _ => src.regs
/-- Live-in of a sequence from its live-out. -/
def liveIn : List (Instr L O P H) → Finset Nat → Finset Nat
  | [], out => out
  | i :: rest, out => liveStep i (liveIn rest out)
end

end Liveness

/-- Two outcomes that code reading only the registers `out` afterwards cannot tell apart. -/
def Outcome.Agree (out : Finset Nat) : Outcome V → Outcome V → Prop
  | .next R₁, .next R₂ => ∀ i ∈ out, R₁ i = R₂ i
  | .ret v₁, .ret v₂ => v₁ = v₂
  | _, _ => False

/-! ## Sequencing -/

section Sequencing
variable (S : Sem V L O P H) (ans : H → List V → Option V)

theorem andThen_assoc (o : Option (Outcome V)) (k₁ k₂ : Regs V → Option (Outcome V)) :
    andThen (andThen o k₁) k₂ = andThen o fun R => andThen (k₁ R) k₂ := by
  rcases o with _ | _ | _ <;> rfl

theorem andThen_next_eq (o : Option (Outcome V)) : andThen o (fun R => some (.next R)) = o := by
  rcases o with _ | _ | _ <;> rfl

theorem exec_append (c₁ c₂ : List (Instr L O P H)) (R : Regs V) :
    exec S ans (c₁ ++ c₂) R = andThen (exec S ans c₁ R) (exec S ans c₂) := by
  induction c₁ generalizing R with
  | nil => rfl
  | cons i rest ih =>
      have ih' : exec S ans (rest ++ c₂) = fun R => andThen (exec S ans rest R) (exec S ans c₂) :=
        funext ih
      simp only [List.cons_append, exec, andThen_assoc, ih']

theorem exec_singleton (i : Instr L O P H) (R : Regs V) :
    exec S ans [i] R = step S ans i R :=
  andThen_next_eq _

theorem read_congr {R₁ R₂ : Regs V} {a : Operand L} (h : ∀ i ∈ a.regs, R₁ i = R₂ i) :
    read S R₁ a = read S R₂ a := by
  cases a with
  | reg i => exact h i (by simp [Operand.regs])
  | lit l => rfl

theorem readAll_congr {R₁ R₂ : Regs V} :
    ∀ {args : List (Operand L)}, (∀ i ∈ operandRegs args, R₁ i = R₂ i) →
      readAll S R₁ args = readAll S R₂ args
  | [], _ => rfl
  | a :: as, h => by
      simp only [readAll]
      rw [read_congr S (fun i hi => h i (by simp [operandRegs, hi])),
        readAll_congr (fun i hi => h i (by simp [operandRegs, hi]))]

end Sequencing

/-! ## Lowering preserves meaning -/

/-- `R'` keeps `R`'s locals in scope `Γ` and its temporaries in `[m, k)`. -/
def Keeps (m k : Nat) (Γ : Finset Nat) (R R' : Regs V) : Prop :=
  (∀ i ∈ Γ, R' i = R i) ∧ ∀ r, m ≤ r → r < k → R' r = R r

theorem Keeps.refl (m k : Nat) (Γ : Finset Nat) (R : Regs V) : Keeps m k Γ R R :=
  ⟨fun _ _ => rfl, fun _ _ _ => rfl⟩

theorem Keeps.trans {m k k' : Nat} {Γ : Finset Nat} {R R₁ R₂ : Regs V}
    (h₁ : Keeps m k Γ R R₁) (h₂ : Keeps m k' Γ R₁ R₂) (hk : k ≤ k') : Keeps m k Γ R R₂ :=
  ⟨fun i hi => (h₂.1 i hi).trans (h₁.1 i hi),
   fun r hr hrk => (h₂.2 r hr (lt_of_lt_of_le hrk hk)).trans (h₁.2 r hr hrk)⟩

/-- Operand `a` reads `w` from every register file that keeps `R'`'s scope `Γ` and its
temporaries in `[m, k)`. -/
def ReadsFrom (S : Sem V L O P H) (m k : Nat) (Γ : Finset Nat) (a : Operand L) (R' : Regs V)
    (w : Option V) : Prop :=
  ∀ R'', Keeps m k Γ R' R'' → read S R'' a = w

/-- The code computing operands, against the node executor evaluating the same nodes: both
decline; or the code falls through keeping the scope and the temporaries below `next`, the
operands read the node executor's values (`reads`), and every local on which the registers
agreed still agrees; or the node executor declined reading a local that the code reads only
when an instruction consumes the operand (`late`). -/
inductive Staged {α : Type} (m next : Nat) (Γ : Finset Nat) (R N : Regs V)
    (reads : Regs V → Option α → Prop) : Option (α × Regs V) → Option (Outcome V) → Prop
  | decline : Staged m next Γ R N reads none none
  | fell {x : α} {N' R' : Regs V} : Keeps m next Γ R R' → reads R' (some x) →
      (∀ i < m, R i = N i → R' i = N' i) →
      Staged m next Γ R N reads (some (x, N')) (some (.next R'))
  | late {R' : Regs V} : Keeps m next Γ R R' → reads R' none →
      Staged m next Γ R N reads none (some (.next R'))

/-- Code lowered into `dst`, against the node executor: both decline, or the code falls
through with the value in `dst`, the scope and the other temporaries below `next` kept, and
every local on which the registers agreed still agreeing. -/
inductive Lands (m dst next : Nat) (Γ : Finset Nat) (R N : Regs V) :
    Option (V × Regs V) → Option (Outcome V) → Prop
  | decline : Lands m dst next Γ R N none none
  | fell {v : V} {N' R' : Regs V} : R' dst = some v →
      (∀ r, m ≤ r → r < next → r ≠ dst → R' r = R r) → (∀ i ∈ Γ, R' i = R i) →
      (∀ i < m, R i = N i → R' i = N' i) →
      Lands m dst next Γ R N (some (v, N')) (some (.next R'))

/-- Tail code, against the node executor: both decline, or the body answers the value. -/
inductive Answers : Option (V × Regs V) → Option (Outcome V) → Prop
  | decline : Answers none none
  | ret {v : V} {N' : Regs V} : Answers (some (v, N')) (some (.ret v))

/-- Lowered code against the node executor: `Answers` in tail position, `Lands` otherwise. -/
def Lowered (tail : Bool) (m dst next : Nat) (Γ : Finset Nat) (R N : Regs V) :
    Option (V × Regs V) → Option (Outcome V) → Prop :=
  match tail with
  | true => Answers
  | false => Lands m dst next Γ R N

theorem Lowered.decline (tail : Bool) (m dst next : Nat) (Γ : Finset Nat) (R N : Regs V) :
    Lowered tail m dst next Γ R N none none := by
  cases tail
  · exact Lands.decline
  · exact Answers.decline

theorem Lowered.shift {tail : Bool} {m dst next next₁ : Nat} {Γ Γ₁ : Finset Nat}
    {R N R₁ N₁ : Regs V} (hk : Keeps m next Γ R R₁) (hag : ∀ i < m, R i = N i → R₁ i = N₁ i)
    (hle : next ≤ next₁) (hΓ : Γ ⊆ Γ₁) {x : Option (V × Regs V)} {o : Option (Outcome V)}
    (h : Lowered tail m dst next₁ Γ₁ R₁ N₁ x o) : Lowered tail m dst next Γ R N x o := by
  cases tail with
  | true => exact h
  | false =>
      change Lands m dst next₁ Γ₁ R₁ N₁ x o at h
      cases h with
      | decline => exact Lands.decline
      | fell hd ht hs ha =>
          exact Lands.fell hd
            (fun r hr hrn hrd => (ht r hr (lt_of_lt_of_le hrn hle) hrd).trans (hk.2 r hr hrn))
            (fun i hi => (hs i (hΓ hi)).trans (hk.1 i hi)) (fun i hi hRN => ha i hi (hag i hi hRN))

theorem Staged.compose {α : Type} {m next : Nat} {Γ : Finset Nat} {R N : Regs V}
    {rd : Regs V → Option α → Prop} {x : Option (α × Regs V)} {o : Option (Outcome V)}
    {Rel : Option (V × Regs V) → Option (Outcome V) → Prop}
    {f : α × Regs V → Option (V × Regs V)} {k : Regs V → Option (Outcome V)}
    (h : Staged m next Γ R N rd x o) (hdecline : Rel none none)
    (hfell : ∀ a N' R', Keeps m next Γ R R' → rd R' (some a) →
      (∀ i < m, R i = N i → R' i = N' i) → Rel (f (a, N')) (k R'))
    (hlate : ∀ R', Keeps m next Γ R R' → rd R' none → k R' = none) :
    Rel (x.bind f) (andThen o k) := by
  cases h with
  | decline => exact hdecline
  | fell hk hrd hag => exact hfell _ _ _ hk hrd hag
  | late hk hrd => simpa [andThen, hlate _ hk hrd] using hdecline

section Mono
variable (fuses : O → Nat → Bool)

theorem operand_next_le (e : Node L O P H) {next : Nat} {low : List (Instr L O P H) × Nat}
    (h : next ≤ low.2) : next ≤ (operand e next low).2.2 := by
  cases e <;> simp [operand, h]

/-- Lowering allocates registers upward. -/
theorem compile_mono :
    (∀ (e : Node L O P H) (tail : Bool) (dst next : Nat),
      next ≤ (compile fuses e tail dst next).2) ∧
    (∀ (cs : List (Node L O P H)) (next : Nat), next ≤ (compileArgs fuses cs next).2.2) := by
  refine compile.mutual_induct fuses
    (fun e tail dst next => next ≤ (compile fuses e tail dst next).2)
    (fun cs next => next ≤ (compileArgs fuses cs next).2.2) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro l tail dst next; simp [compile]
  · intro i tail dst next; simp [compile]
  · intro o cs tail dst next ih; simp only [compile]; omega
  · intro o cs t e tail dst next hf; dsimp only; intro ihcs iht ihe
    rw [compile.eq_4, if_pos hf]; dsimp only; omega
  · intro o cs t e tail dst next hf; dsimp only; intro ihc iht ihe
    rw [compile.eq_4, if_neg hf]; dsimp only; omega
  · intro c t e tail dst next hc; dsimp only; intro ihc iht ihe
    rw [compile.eq_5 _ _ _ _ _ _ _ hc]
    have := operand_next_le c (next := next)
      (low := compile fuses c false next (next + 1)) (by omega)
    dsimp only; omega
  · intro c p b tail dst next; dsimp only; intro ihc ihb
    have := operand_next_le c (next := next)
      (low := compile fuses c false next (next + 1)) (by omega)
    simp only [compile]; omega
  · intro h cs tail dst next ih; simp only [compile]; omega
  · intro next; simp [compileArgs]
  · intro c cs next; dsimp only; intro ihc ihcs
    have := operand_next_le c (next := next)
      (low := compile fuses c false next (next + 1)) (by omega)
    simp only [compileArgs]; omega

end Mono

section Correct
variable (S : Sem V L O P H) (ans : H → List V → Option V) (fuses : O → Nat → Bool) (m : Nat)

/-- What lowering node `e` guarantees, for every scope, register files agreeing on it, and
free registers from `next` up (above the `m` locals): in tail position the code answers exactly
the node executor's value; otherwise it lands the value in `dst`, a register below `next`. -/
def LowerOk (e : Node L O P H) (tail : Bool) (dst next : Nat) : Prop :=
  ∀ (Γ : Finset Nat) (R N : Regs V), Scoped S.toPatterns m Γ e → (∀ i ∈ Γ, i < m) →
    (∀ i ∈ Γ, R i = N i) → m ≤ next → (tail = false → m ≤ dst ∧ dst < next) →
    Lowered tail m dst next Γ R N (eval S ans N e) (exec S ans (compile fuses e tail dst next).1 R)

/-- What lowering children to operands guarantees. -/
def ArgsOk (cs : List (Node L O P H)) (next : Nat) : Prop :=
  ∀ (Γ : Finset Nat) (R N : Regs V), ScopedArgs S.toPatterns m Γ cs → (∀ i ∈ Γ, i < m) →
    (∀ i ∈ Γ, R i = N i) → m ≤ next →
    Staged m next Γ R N (fun R' w => readAll S R' (compileArgs fuses cs next).2.1 = w)
      (evalList S ans N cs) (exec S ans (compileArgs fuses cs next).1 R)

theorem staged_of_lands {next k : Nat} {Γ : Finset Nat} {R N : Regs V}
    {x : Option (V × Regs V)} {o : Option (Outcome V)}
    (h : Lands m next (next + 1) Γ R N x o) (hm : m ≤ next) (hk : next < k) :
    Staged m next Γ R N (ReadsFrom S m k Γ (.reg next)) x o := by
  cases h with
  | decline => exact Staged.decline
  | fell hd ht hs ha =>
      refine Staged.fell ⟨hs, fun r hr hrn => ht r hr (by omega) (by omega)⟩ ?_ ha
      intro R'' hk''
      exact (hk''.2 next hm hk).trans hd

theorem operand_staged {c : Node L O P H} {next : Nat}
    (ih : LowerOk S ans fuses m c false next (next + 1)) {Γ : Finset Nat} {R N : Regs V}
    (hs : Scoped S.toPatterns m Γ c) (hΓ : ∀ i ∈ Γ, i < m) (hRN : ∀ i ∈ Γ, R i = N i)
    (hm : m ≤ next) :
    Staged m next Γ R N
      (ReadsFrom S m (operand c next (compile fuses c false next (next + 1))).2.2 Γ
        (operand c next (compile fuses c false next (next + 1))).2.1)
      (eval S ans N c)
      (exec S ans (operand c next (compile fuses c false next (next + 1))).1 R) := by
  have hlt : next < (compile fuses c false next (next + 1)).2 :=
    (compile_mono fuses).1 c false next (next + 1)
  have hlow := ih Γ R N hs hΓ hRN (by omega) (fun _ => ⟨hm, by omega⟩)
  cases c with
  | lit l => exact Staged.fell (Keeps.refl _ _ _ _) (fun _ _ => rfl) (fun _ _ h => h)
  | slot i =>
      have hi : i ∈ Γ := hs
      have hread : ∀ R'', Keeps m next Γ R R'' → read S R'' (.reg i) = N i :=
        fun R'' hk => (hk.1 i hi).trans (hRN i hi)
      show Staged m next Γ R N (ReadsFrom S m next Γ (.reg i)) ((N i).map fun v => (v, N))
        (some (.next R))
      cases hNi : N i with
      | none => exact Staged.late (Keeps.refl _ _ _ _) fun R'' hk => (hread R'' hk).trans hNi
      | some v =>
          exact Staged.fell (Keeps.refl _ _ _ _) (fun R'' hk => (hread R'' hk).trans hNi)
            fun _ _ h => h
  | op o cs => exact staged_of_lands S m hlow hm hlt
  | ite c t e => exact staged_of_lands S m hlow hm hlt
  | bind c p b => exact staged_of_lands S m hlow hm hlt
  | call h cs => exact staged_of_lands S m hlow hm hlt

theorem lands_update {dst next : Nat} {Γ : Finset Nat} {R N R' N' : Regs V} {v : V}
    (hΓ : ∀ i ∈ Γ, i < m) (hdst : m ≤ dst) (hk : Keeps m next Γ R R')
    (hag : ∀ i < m, R i = N i → R' i = N' i) :
    Lands m dst next Γ R N (some (v, N')) (some (.next (Function.update R' dst (some v)))) :=
  Lands.fell (by simp) (fun r hr hrn hrd => by simp [hrd, hk.2 r hr hrn])
    (fun i hi => by simp [(lt_of_lt_of_le (hΓ i hi) hdst).ne, hk.1 i hi])
    (fun i hi h => by simpa [(lt_of_lt_of_le hi hdst).ne] using hag i hi h)

theorem lowerOk_lit (l : L) (tail : Bool) (dst next : Nat) :
    LowerOk S ans fuses m (.lit l) tail dst next := by
  intro Γ R N _ hΓ _ _ hd
  cases tail with
  | true => exact Answers.ret
  | false => exact lands_update m hΓ (hd rfl).1 (Keeps.refl _ _ _ _) fun _ _ h => h

theorem lowerOk_slot (i : Nat) (tail : Bool) (dst next : Nat) :
    LowerOk S ans fuses m (.slot i) tail dst next := by
  intro Γ R N hs hΓ hRN _ hd
  have hR : R i = N i := hRN i hs
  cases tail with
  | true =>
      show Answers ((N i).map fun v => (v, N)) (andThen ((R i).map Outcome.ret) (exec S ans []))
      rw [hR]
      cases N i with
      | none => exact Answers.decline
      | some v => exact Answers.ret
  | false =>
      show Lands m dst next Γ R N ((N i).map fun v => (v, N))
        (andThen ((R i).map fun v => Outcome.next (Function.update R dst (some v)))
          (exec S ans []))
      rw [hR]
      cases N i with
      | none => exact Lands.decline
      | some v => exact lands_update m hΓ (hd rfl).1 (Keeps.refl _ _ _ _) fun _ _ h => h

theorem lowerOk_op (o : O) (cs : List (Node L O P H)) (tail : Bool) (dst next : Nat)
    (ih : ArgsOk S ans fuses m cs next) : LowerOk S ans fuses m (.op o cs) tail dst next := by
  intro Γ R N hs hΓ hRN hm hd
  have hA := ih Γ R N hs hΓ hRN hm
  cases tail with
  | true =>
      change Answers ((evalList S ans N cs).bind fun r => (S.op o r.1).map fun v => (v, r.2))
        (exec S ans ((compileArgs fuses cs next).1 ++
          [.opRet o (compileArgs fuses cs next).2.1]) R)
      rw [exec_append]
      refine hA.compose Answers.decline ?_ ?_
      · intro vs N' R' _ hrd _
        cases hv : S.op o vs with
        | none => simp [exec, step, hrd, hv, andThen]; exact Answers.decline
        | some v => simp [exec, step, hrd, hv, andThen]; exact Answers.ret
      · intro R' _ hrd
        simp [exec, step, hrd, andThen]
  | false =>
      obtain ⟨hdst, -⟩ := hd rfl
      change Lands m dst next Γ R N
        ((evalList S ans N cs).bind fun r => (S.op o r.1).map fun v => (v, r.2))
        (exec S ans ((compileArgs fuses cs next).1 ++
          [.op dst o (compileArgs fuses cs next).2.1]) R)
      rw [exec_append]
      refine hA.compose Lands.decline ?_ ?_
      · intro vs N' R' hk hrd hag
        cases hv : S.op o vs with
        | none => simp [exec, step, hrd, hv, andThen]; exact Lands.decline
        | some v =>
            simp only [exec, step, hrd, hv, andThen, Option.bind_some, Option.map_some]
            exact lands_update m hΓ hdst hk hag
      · intro R' _ hrd
        simp [exec, step, hrd, andThen]

theorem lowerOk_call (h : H) (cs : List (Node L O P H)) (tail : Bool) (dst next : Nat)
    (ih : ArgsOk S ans fuses m cs next) : LowerOk S ans fuses m (.call h cs) tail dst next := by
  intro Γ R N hs hΓ hRN hm hd
  have hA := ih Γ R N hs hΓ hRN hm
  cases tail with
  | true =>
      change Answers ((evalList S ans N cs).bind fun r => (ans h r.1).map fun v => (v, r.2))
        (exec S ans ((compileArgs fuses cs next).1 ++
          [.tailCall h (compileArgs fuses cs next).2.1]) R)
      rw [exec_append]
      refine hA.compose Answers.decline ?_ ?_
      · intro vs N' R' _ hrd _
        cases hv : ans h vs with
        | none => simp [exec, step, hrd, hv, andThen]; exact Answers.decline
        | some v => simp [exec, step, hrd, hv, andThen]; exact Answers.ret
      · intro R' _ hrd
        simp [exec, step, hrd, andThen]
  | false =>
      obtain ⟨hdst, -⟩ := hd rfl
      change Lands m dst next Γ R N
        ((evalList S ans N cs).bind fun r => (ans h r.1).map fun v => (v, r.2))
        (exec S ans ((compileArgs fuses cs next).1 ++
          [.call dst h (compileArgs fuses cs next).2.1]) R)
      rw [exec_append]
      refine hA.compose Lands.decline ?_ ?_
      · intro vs N' R' hk hrd hag
        cases hv : ans h vs with
        | none => simp [exec, step, hrd, hv, andThen]; exact Lands.decline
        | some v =>
            simp only [exec, step, hrd, hv, andThen, Option.bind_some, Option.map_some]
            exact lands_update m hΓ hdst hk hag
      · intro R' _ hrd
        simp [exec, step, hrd, andThen]

theorem lowerOk_ite_plain {c t e : Node L O P H} {tail : Bool} {dst next : Nat}
    (a : List (Instr L O P H) × Operand L × Nat)
    (hcode : (compile fuses (.ite c t e) tail dst next).1 =
      a.1 ++ [.ite a.2.1 (compile fuses t tail dst a.2.2).1
        (compile fuses e tail dst (compile fuses t tail dst a.2.2).2).1])
    (hstage : ∀ (Γ : Finset Nat) (R N : Regs V), Scoped S.toPatterns m Γ c →
      (∀ i ∈ Γ, i < m) → (∀ i ∈ Γ, R i = N i) → m ≤ next →
      Staged m next Γ R N (ReadsFrom S m a.2.2 Γ a.2.1) (eval S ans N c) (exec S ans a.1 R))
    (hmono : next ≤ a.2.2) (iht : LowerOk S ans fuses m t tail dst a.2.2)
    (ihe : LowerOk S ans fuses m e tail dst (compile fuses t tail dst a.2.2).2) :
    LowerOk S ans fuses m (.ite c t e) tail dst next := by
  intro Γ R N hs hΓ hRN hm hd
  obtain ⟨hsc, hst, hse⟩ := hs
  have hmono' : a.2.2 ≤ (compile fuses t tail dst a.2.2).2 :=
    (compile_mono fuses).1 t tail dst a.2.2
  rw [hcode, exec_append]
  refine (hstage Γ R N hsc hΓ hRN hm).compose (Lowered.decline ..) ?_ ?_
  · intro v N' R' hk hrd hag
    have hRN' : ∀ i ∈ Γ, R' i = N' i := fun i hi => hag i (hΓ i hi) (hRN i hi)
    have hread : read S R' a.2.1 = some v := hrd R' (Keeps.refl _ _ _ _)
    rw [exec_singleton]
    simp only [step, hread, Option.bind_some]
    cases hb : S.truth v with
    | none => exact Lowered.decline ..
    | some b =>
        cases b with
        | true =>
            simpa using Lowered.shift hk hag hmono (Finset.Subset.refl Γ)
              (iht Γ R' N' hst hΓ hRN' (by omega) fun h => ⟨(hd h).1, by have := (hd h).2; omega⟩)
        | false =>
            simpa using Lowered.shift hk hag (hmono.trans hmono') (Finset.Subset.refl Γ)
              (ihe Γ R' N' hse hΓ hRN' (by omega) fun h => ⟨(hd h).1, by have := (hd h).2; omega⟩)
  · intro R' _ hrd
    rw [exec_singleton]
    simp [step, hrd R' (Keeps.refl _ _ _ _)]

theorem lowerOk_ite_fused (o : O) (cs : List (Node L O P H)) (t e : Node L O P H) (tail : Bool)
    (dst next : Nat) (hf : fuses o cs.length = true) (ihcs : ArgsOk S ans fuses m cs next)
    (iht : LowerOk S ans fuses m t tail dst (compileArgs fuses cs next).2.2)
    (ihe : LowerOk S ans fuses m e tail dst
      (compile fuses t tail dst (compileArgs fuses cs next).2.2).2) :
    LowerOk S ans fuses m (.ite (.op o cs) t e) tail dst next := by
  intro Γ R N hs hΓ hRN hm hd
  obtain ⟨hsc, hst, hse⟩ := hs
  have hmono : next ≤ (compileArgs fuses cs next).2.2 := (compile_mono fuses).2 cs next
  have hmono' := (compile_mono fuses).1 t tail dst (compileArgs fuses cs next).2.2
  have heval : eval S ans N (.ite (.op o cs) t e) = (evalList S ans N cs).bind fun r =>
      (S.op o r.1).bind fun v => (S.truth v).bind fun b =>
        if b then eval S ans r.2 t else eval S ans r.2 e := by
    simp only [eval, Option.bind_assoc]
    congr 1; funext r
    cases S.op o r.1 <;> rfl
  rw [compile.eq_4, if_pos hf, heval]
  dsimp only
  rw [exec_append]
  refine (ihcs Γ R N hsc hΓ hRN hm).compose (Lowered.decline ..) ?_ ?_
  · intro vs N' R' hk hrd hag
    have hRN' : ∀ i ∈ Γ, R' i = N' i := fun i hi => hag i (hΓ i hi) (hRN i hi)
    rw [exec_singleton]
    simp only [step, hrd, Option.bind_some]
    cases hv : S.op o vs with
    | none => exact Lowered.decline ..
    | some v =>
        simp only [Option.bind_some]
        cases hb : S.truth v with
        | none => exact Lowered.decline ..
        | some b =>
            cases b with
            | true =>
                simpa using Lowered.shift hk hag hmono (Finset.Subset.refl Γ)
                  (iht Γ R' N' hst hΓ hRN' (by omega)
                    fun h => ⟨(hd h).1, by have := (hd h).2; omega⟩)
            | false =>
                simpa using Lowered.shift hk hag (hmono.trans hmono') (Finset.Subset.refl Γ)
                  (ihe Γ R' N' hse hΓ hRN' (by omega)
                    fun h => ⟨(hd h).1, by have := (hd h).2; omega⟩)
  · intro R' _ hrd
    rw [exec_singleton]
    simp [step, hrd]

theorem lowerOk_bind (c : Node L O P H) (p : P) (b : Node L O P H) (tail : Bool) (dst next : Nat)
    (ihc : LowerOk S ans fuses m c false next (next + 1))
    (ihb : LowerOk S ans fuses m b tail dst
      (operand c next (compile fuses c false next (next + 1))).2.2) :
    LowerOk S ans fuses m (.bind c p b) tail dst next := by
  intro Γ R N hs hΓ hRN hm hd
  obtain ⟨hsc, hreads, hslots, hsb⟩ := hs
  have hmono : next ≤ (operand c next (compile fuses c false next (next + 1))).2.2 :=
    operand_next_le c (by have := (compile_mono fuses).1 c false next (next + 1); omega)
  change Lowered tail m dst next Γ R N
    ((eval S ans N c).bind fun r => (S.bindLet p r.1 r.2).bind fun N' => eval S ans N' b)
    (exec S ans ((operand c next (compile fuses c false next (next + 1))).1 ++
      .bind (operand c next (compile fuses c false next (next + 1))).2.1 p ::
        (compile fuses b tail dst
          (operand c next (compile fuses c false next (next + 1))).2.2).1) R)
  rw [exec_append]
  refine (operand_staged S ans fuses m ihc hsc hΓ hRN hm).compose (Lowered.decline ..) ?_ ?_
  · intro v N₁ R₁ hk hrd hag
    have hread := hrd R₁ (Keeps.refl _ _ _ _)
    simp only [exec, step, hread, Option.bind_some]
    have hloc := S.bindLet_local (p := p) (v := v) (R₁ := R₁) (R₂ := N₁)
      (fun i hi => hag i (hΓ i (hreads i hi)) (hRN i (hreads i hi)))
    generalize hx : S.bindLet p v R₁ = x at hloc ⊢
    generalize hy : S.bindLet p v N₁ = y at hloc ⊢
    cases hloc with
    | none => exact Lowered.decline ..
    | @some R₂ N₂ hsl =>
        have fR := S.bindLet_frame hx
        have fN := S.bindLet_frame hy
        have hk₂ : Keeps m next Γ R R₂ :=
          ⟨fun i hi => (fR i fun hs => (hslots i hs).2 hi).trans (hk.1 i hi),
           fun r hr hrn => (fR r fun hs => absurd hr (not_le.2 (hslots r hs).1)).trans
             (hk.2 r hr hrn)⟩
        have hag₂ : ∀ i < m, R i = N i → R₂ i = N₂ i := by
          intro i hi h
          by_cases hs : i ∈ S.patSlots p
          · exact hsl i hs
          · rw [fR i hs, fN i hs]; exact hag i hi h
        have hΓ₂ : ∀ i ∈ Γ ∪ (S.patSlots p).toFinset, i < m := by
          intro i hi
          rcases Finset.mem_union.1 hi with hi | hi
          · exact hΓ i hi
          · exact (hslots i (List.mem_toFinset.1 hi)).1
        have hRN₂ : ∀ i ∈ Γ ∪ (S.patSlots p).toFinset, R₂ i = N₂ i := by
          intro i hi
          rcases Finset.mem_union.1 hi with hi | hi
          · exact hag₂ i (hΓ i hi) (hRN i hi)
          · exact hsl i (List.mem_toFinset.1 hi)
        exact Lowered.shift hk₂ hag₂ hmono Finset.subset_union_left
          (ihb _ R₂ N₂ hsb hΓ₂ hRN₂ (by omega) fun h => ⟨(hd h).1, by have := (hd h).2; omega⟩)
  · intro R' _ hrd
    simp [exec, step, hrd R' (Keeps.refl _ _ _ _), andThen]

theorem argsOk_nil (next : Nat) : ArgsOk S ans fuses m [] next := by
  intro Γ R N _ _ _ _
  exact Staged.fell (Keeps.refl _ _ _ _) rfl fun _ _ h => h

theorem argsOk_cons (c : Node L O P H) (cs : List (Node L O P H)) (next : Nat)
    (ihc : LowerOk S ans fuses m c false next (next + 1))
    (ihcs : ArgsOk S ans fuses m cs (operand c next (compile fuses c false next (next + 1))).2.2) :
    ArgsOk S ans fuses m (c :: cs) next := by
  intro Γ R N hs hΓ hRN hm
  obtain ⟨hsc, hscs⟩ := hs
  have hmono : next ≤ (operand c next (compile fuses c false next (next + 1))).2.2 :=
    operand_next_le c (by have := (compile_mono fuses).1 c false next (next + 1); omega)
  change Staged m next Γ R N
    (fun R' w => readAll S R' ((operand c next (compile fuses c false next (next + 1))).2.1 ::
      (compileArgs fuses cs (operand c next (compile fuses c false next (next + 1))).2.2).2.1) = w)
    ((eval S ans N c).bind fun x => (evalList S ans x.2 cs).map fun rs => (x.1 :: rs.1, rs.2))
    (exec S ans ((operand c next (compile fuses c false next (next + 1))).1 ++
      (compileArgs fuses cs (operand c next (compile fuses c false next (next + 1))).2.2).1) R)
  rw [exec_append]
  have hA := operand_staged S ans fuses m ihc hsc hΓ hRN hm
  generalize eval S ans N c = x at hA ⊢
  generalize exec S ans (operand c next (compile fuses c false next (next + 1))).1 R = o at hA ⊢
  cases hA with
  | decline => exact Staged.decline
  | @fell v N₁ R₁ hk hrd hag =>
      simp only [Option.bind_some, andThen]
      have hB := ihcs Γ R₁ N₁ hscs hΓ (fun i hi => hag i (hΓ i hi) (hRN i hi)) (by omega)
      generalize evalList S ans N₁ cs = y at hB ⊢
      generalize exec S ans _ R₁ = q at hB ⊢
      cases hB with
      | decline => exact Staged.decline
      | @fell vs N₂ R₂ hk₂ hrd₂ hag₂ =>
          refine Staged.fell (hk.trans hk₂ hmono) ?_ fun i hi h => hag₂ i hi (hag i hi h)
          simp [readAll, hrd R₂ hk₂, hrd₂]
      | late hk₂ hrd₂ =>
          refine Staged.late (hk.trans hk₂ hmono) ?_
          simp [readAll, hrd _ hk₂, hrd₂]
  | @late R₁ hk hrd =>
      simp only [Option.bind_none, andThen]
      have hB := ihcs Γ R₁ R₁ hscs hΓ (fun _ _ => rfl) (by omega)
      generalize evalList S ans R₁ cs = y at hB ⊢
      generalize exec S ans _ R₁ = q at hB ⊢
      cases hB with
      | decline => exact Staged.decline
      | fell hk₂ _ _ => exact Staged.late (hk.trans hk₂ hmono) (by simp [readAll, hrd _ hk₂])
      | late hk₂ _ => exact Staged.late (hk.trans hk₂ hmono) (by simp [readAll, hrd _ hk₂])

/-- Lowering, for every node and every lowering call the lowering makes. -/
theorem lower_ok :
    (∀ (e : Node L O P H) (tail : Bool) (dst next : Nat), LowerOk S ans fuses m e tail dst next) ∧
    (∀ (cs : List (Node L O P H)) (next : Nat), ArgsOk S ans fuses m cs next) :=
  compile.mutual_induct fuses (LowerOk S ans fuses m) (ArgsOk S ans fuses m)
    (lowerOk_lit S ans fuses m) (lowerOk_slot S ans fuses m)
    (lowerOk_op S ans fuses m)
    (lowerOk_ite_fused S ans fuses m)
    (fun o cs t e tail dst next hf ihc iht ihe =>
      lowerOk_ite_plain S ans fuses m
        (operand (.op o cs) next (compile fuses (.op o cs) false next (next + 1)))
        (by rw [compile.eq_4, if_neg hf]; rfl)
        (fun _ _ _ hs hΓ hRN hm => operand_staged S ans fuses m ihc hs hΓ hRN hm)
        (by have := (compile_mono fuses).1 (.op o cs) false next (next + 1)
            simp only [operand]; omega)
        iht ihe)
    (fun c t e tail dst next hc ihc iht ihe =>
      lowerOk_ite_plain S ans fuses m (operand c next (compile fuses c false next (next + 1)))
        (by rw [compile.eq_5 _ _ _ _ _ _ _ hc])
        (fun _ _ _ hs hΓ hRN hm => operand_staged S ans fuses m ihc hs hΓ hRN hm)
        (operand_next_le c (by have := (compile_mono fuses).1 c false next (next + 1); omega))
        iht ihe)
    (lowerOk_bind S ans fuses m) (lowerOk_call S ans fuses m)
    (argsOk_nil S ans fuses m) (argsOk_cons S ans fuses m)

end Correct

section Main
variable (S : Sem V L O P H) (ans : H → List V → Option V) (fuses : O → Nat → Bool)

/-- **Lowering into a register preserves meaning.**  For a node scoped in `Γ` (locals below
`m`), code registers `R` agreeing with the node executor's `N` on the scope, and a destination
`dst` allocated before the node's temporaries: the code declines exactly when the node executor
does, and otherwise falls through with the value in `dst`, the scope and the other registers
below `next` kept, and every local on which the registers agreed still agreeing. -/
theorem lower_lands {m : Nat} {e : Node L O P H} {Γ : Finset Nat} {dst next : Nat}
    {R N : Regs V} (hs : Scoped S.toPatterns m Γ e) (hΓ : ∀ i ∈ Γ, i < m)
    (hRN : ∀ i ∈ Γ, R i = N i) (hdst : m ≤ dst) (hdn : dst < next) :
    Lands m dst next Γ R N (eval S ans N e) (exec S ans (compile fuses e false dst next).1 R) :=
  (lower_ok S ans fuses m).1 e false dst next Γ R N hs hΓ hRN (by omega) fun _ => ⟨hdst, hdn⟩

/-- **Lowering in tail position preserves meaning.**  The code declines exactly when the node
executor does, and otherwise answers its value. -/
theorem lower_answers {m : Nat} {e : Node L O P H} {Γ : Finset Nat} {dst next : Nat}
    {R N : Regs V} (hs : Scoped S.toPatterns m Γ e) (hΓ : ∀ i ∈ Γ, i < m)
    (hRN : ∀ i ∈ Γ, R i = N i) (hm : m ≤ next) :
    Answers (eval S ans N e) (exec S ans (compile fuses e true dst next).1 R) :=
  (lower_ok S ans fuses m).1 e true dst next Γ R N hs hΓ hRN hm (by simp)

/-- **An answer producer's step preserves meaning.**  A step's region runs over the frame's slots
(the locals below `m`) as `stepCode`, lowered into register `m` and returned, never ending in a
tail call, which would reuse the slots the search reads after the step.  That code declines
exactly when the node executor declines on the region, and otherwise answers its value. -/
theorem lower_step_answers {m : Nat} {e : Node L O P H} {Γ : Finset Nat} {R N : Regs V}
    (hs : Scoped S.toPatterns m Γ e) (hΓ : ∀ i ∈ Γ, i < m) (hRN : ∀ i ∈ Γ, R i = N i) :
    Answers (eval S ans N e) (exec S ans (stepCode fuses e m) R) := by
  have hl := lower_lands S ans fuses hs hΓ hRN (le_refl m) (Nat.lt_succ_self m)
  rw [stepCode, exec_append]
  generalize exec S ans (compile fuses e false m (m + 1)).1 R = o at hl ⊢
  generalize eval S ans N e = x at hl ⊢
  cases hl with
  | decline => exact Answers.decline
  | fell hd _ _ _ =>
      simp only [andThen, exec_singleton, step, read, hd, Option.map_some]
      exact Answers.ret

/-- The frame's slots after a step: when the node executor answers `(v, N')`, the step's code
reaches its return with `v` in register `m` and every slot on which the registers agreed still
agreeing; the return writes no register, so the search reads the same slots after either
executor. -/
theorem lower_step_slots {m : Nat} {e : Node L O P H} {Γ : Finset Nat} {R N : Regs V}
    (hs : Scoped S.toPatterns m Γ e) (hΓ : ∀ i ∈ Γ, i < m) (hRN : ∀ i ∈ Γ, R i = N i)
    {v : V} {N' : Regs V} (h : eval S ans N e = some (v, N')) :
    ∃ R', exec S ans (compile fuses e false m (m + 1)).1 R = some (.next R') ∧
      R' m = some v ∧ ∀ i < m, R i = N i → R' i = N' i := by
  have hl := lower_lands S ans fuses hs hΓ hRN (le_refl m) (Nat.lt_succ_self m)
  rw [h] at hl
  generalize exec S ans (compile fuses e false m (m + 1)).1 R = o at hl ⊢
  cases hl with
  | fell hd _ _ ha => exact ⟨_, rfl, hd, ha⟩

/-- Tail code's answer is the node executor's value. -/
theorem Answers.answer_eq {x : Option (V × Regs V)} {o : Option (Outcome V)}
    (h : Answers x o) : answer o = x.map Prod.fst := by
  cases h <;> rfl

/-- **The register machine answers every call as the node executor does**, for every fuel and
whatever the registers of each activation hold outside its bound locals. -/
theorem codeAnswer_eq_nodeAnswer (hS : EntersScoped S) (junk : Nat → H → List V → Regs V) :
    ∀ n, codeAnswer S fuses junk n = nodeAnswer S n
  | 0 => rfl
  | n + 1 => by
      funext h vs
      simp only [codeAnswer, nodeAnswer, codeAnswer_eq_nodeAnswer hS junk n]
      cases he : S.enter h vs with
      | none => rfl
      | some e =>
          obtain ⟨hb, hsc⟩ := hS h vs e he
          exact (lower_answers S (nodeAnswer S n) fuses hsc hb
            (fun i hi => by simp [Entered.fill, hi]) le_rfl).answer_eq

end Main

/-! ## With fuel -/

/-- The node executor with fuel `n`: calls are answered by `nodeAnswer S n`. -/
abbrev evalN (S : Sem V L O P H) (n : Nat) : Regs V → Node L O P H → Option (V × Regs V) :=
  eval S (nodeAnswer S n)

/-- The register machine with fuel `n`, each activation's registers outside its bound locals
holding `junk`. -/
abbrev execN (S : Sem V L O P H) (fuses : O → Nat → Bool) (junk : Nat → H → List V → Regs V)
    (n : Nat) : List (Instr L O P H) → Regs V → Option (Outcome V) :=
  exec S (codeAnswer S fuses junk n)

section Fuel
variable (S : Sem V L O P H) (fuses : O → Nat → Bool) (junk : Nat → H → List V → Regs V)

/-- With fuel `n + 1`, a call evaluates its arguments left to right, enters, and evaluates the
body with fuel `n` in the entered registers; the caller keeps its own registers. -/
theorem evalN_call (n : Nat) (N : Regs V) (h : H) (cs : List (Node L O P H)) :
    evalN S (n + 1) N (.call h cs) = (evalList S (nodeAnswer S (n + 1)) N cs).bind fun r =>
      ((S.enter h r.1).bind fun e => (evalN S n e.regs e.body).map Prod.fst).map
        fun v => (v, r.2) := rfl

/-- Without fuel a call declines. -/
theorem evalN_call_zero (N : Regs V) (h : H) (cs : List (Node L O P H)) :
    evalN S 0 N (.call h cs) = none := by
  change (evalList S (nodeAnswer S 0) N cs).bind _ = none
  cases evalList S (nodeAnswer S 0) N cs <;> rfl

/-- `lower_lands` with fuel. -/
theorem lands_fuel (hS : EntersScoped S) (n : Nat) {m : Nat} {e : Node L O P H}
    {Γ : Finset Nat} {dst next : Nat} {R N : Regs V} (hs : Scoped S.toPatterns m Γ e)
    (hΓ : ∀ i ∈ Γ, i < m) (hRN : ∀ i < m, R i = N i) (hdst : m ≤ dst) (hdn : dst < next) :
    Lands m dst next Γ R N (evalN S n N e)
      (execN S fuses junk n (compile fuses e false dst next).1 R) := by
  rw [execN, codeAnswer_eq_nodeAnswer S fuses hS junk n]
  exact lower_lands S _ fuses hs hΓ (fun i hi => hRN i (hΓ i hi)) hdst hdn

/-- `lower_answers` with fuel. -/
theorem answers_fuel (hS : EntersScoped S) (n : Nat) {m : Nat} {e : Node L O P H}
    {Γ : Finset Nat} {dst next : Nat} {R N : Regs V} (hs : Scoped S.toPatterns m Γ e)
    (hΓ : ∀ i ∈ Γ, i < m) (hRN : ∀ i < m, R i = N i) (hm : m ≤ next) :
    Answers (evalN S n N e) (execN S fuses junk n (compile fuses e true dst next).1 R) := by
  rw [execN, codeAnswer_eq_nodeAnswer S fuses hS junk n]
  exact lower_answers S _ fuses hs hΓ (fun i hi => hRN i (hΓ i hi)) hm

/-- `lower_step_answers` with fuel. -/
theorem lower_step_answers_fuel (hS : EntersScoped S) (n : Nat) {m : Nat} {e : Node L O P H}
    {Γ : Finset Nat} {R N : Regs V} (hs : Scoped S.toPatterns m Γ e) (hΓ : ∀ i ∈ Γ, i < m)
    (hRN : ∀ i < m, R i = N i) :
    Answers (evalN S n N e) (execN S fuses junk n (stepCode fuses e m) R) := by
  rw [execN, codeAnswer_eq_nodeAnswer S fuses hS junk n]
  exact lower_step_answers S _ fuses hs hΓ fun i hi => hRN i (hΓ i hi)

/-- Non-tail lowering, forward: when the node executor answers, the code falls through with the
value in `dst` and the locals agreeing. -/
theorem lower_sound (hS : EntersScoped S) (n : Nat) {m : Nat} {e : Node L O P H}
    {Γ : Finset Nat} {dst next : Nat} {R N : Regs V} (hs : Scoped S.toPatterns m Γ e)
    (hΓ : ∀ i ∈ Γ, i < m) (hRN : ∀ i < m, R i = N i) (hdst : m ≤ dst) (hdn : dst < next)
    {v : V} {N' : Regs V} (h : evalN S n N e = some (v, N')) :
    ∃ R', execN S fuses junk n (compile fuses e false dst next).1 R = some (.next R') ∧
      R' dst = some v ∧ ∀ i < m, R' i = N' i := by
  have hl := lands_fuel S fuses junk hS n hs hΓ hRN hdst hdn
  rw [h] at hl
  generalize execN S fuses junk n _ R = o at hl ⊢
  cases hl with
  | fell hd _ _ ha => exact ⟨_, rfl, hd, fun i hi => ha i hi (hRN i hi)⟩

/-- Non-tail lowering, backward: when the code falls through, the node executor answered the
value in `dst`, with the locals agreeing. -/
theorem lower_complete (hS : EntersScoped S) (n : Nat) {m : Nat} {e : Node L O P H}
    {Γ : Finset Nat} {dst next : Nat} {R N : Regs V} (hs : Scoped S.toPatterns m Γ e)
    (hΓ : ∀ i ∈ Γ, i < m) (hRN : ∀ i < m, R i = N i) (hdst : m ≤ dst) (hdn : dst < next)
    {R' : Regs V}
    (h : execN S fuses junk n (compile fuses e false dst next).1 R = some (.next R')) :
    ∃ v N', evalN S n N e = some (v, N') ∧ R' dst = some v ∧ ∀ i < m, R' i = N' i := by
  have hl := lands_fuel S fuses junk hS n hs hΓ hRN hdst hdn
  rw [h] at hl
  generalize evalN S n N e = x at hl ⊢
  cases hl with
  | fell hd _ _ ha => exact ⟨_, _, rfl, hd, fun i hi => ha i hi (hRN i hi)⟩

/-- Non-tail code never answers for the body. -/
theorem lower_ne_ret (hS : EntersScoped S) (n : Nat) {m : Nat} {e : Node L O P H}
    {Γ : Finset Nat} {dst next : Nat} {R N : Regs V} (hs : Scoped S.toPatterns m Γ e)
    (hΓ : ∀ i ∈ Γ, i < m) (hRN : ∀ i < m, R i = N i) (hdst : m ≤ dst) (hdn : dst < next)
    (v : V) : execN S fuses junk n (compile fuses e false dst next).1 R ≠ some (.ret v) := by
  have hl := lands_fuel S fuses junk hS n hs hΓ hRN hdst hdn
  intro h
  rw [h] at hl
  generalize evalN S n N e = x at hl
  cases hl

/-- Non-tail code declines exactly when the node executor does. -/
theorem lower_none_iff (hS : EntersScoped S) (n : Nat) {m : Nat} {e : Node L O P H}
    {Γ : Finset Nat} {dst next : Nat} {R N : Regs V} (hs : Scoped S.toPatterns m Γ e)
    (hΓ : ∀ i ∈ Γ, i < m) (hRN : ∀ i < m, R i = N i) (hdst : m ≤ dst) (hdn : dst < next) :
    execN S fuses junk n (compile fuses e false dst next).1 R = none ↔ evalN S n N e = none := by
  have hl := lands_fuel S fuses junk hS n hs hΓ hRN hdst hdn
  generalize execN S fuses junk n _ R = o at hl ⊢
  generalize evalN S n N e = x at hl ⊢
  cases hl <;> simp

/-- Tail lowering: the code answers `v` exactly when the node executor's value is `v`. -/
theorem lower_tail_ret_iff (hS : EntersScoped S) (n : Nat) {m : Nat} {e : Node L O P H}
    {Γ : Finset Nat} {dst next : Nat} {R N : Regs V} (hs : Scoped S.toPatterns m Γ e)
    (hΓ : ∀ i ∈ Γ, i < m) (hRN : ∀ i < m, R i = N i) (hm : m ≤ next) (v : V) :
    execN S fuses junk n (compile fuses e true dst next).1 R = some (.ret v) ↔
      ∃ N', evalN S n N e = some (v, N') := by
  have hl := answers_fuel S fuses junk hS n (dst := dst) hs hΓ hRN hm
  generalize execN S fuses junk n _ R = o at hl ⊢
  generalize evalN S n N e = x at hl ⊢
  cases hl with
  | decline => simp
  | ret => simp [eq_comm]

/-- Tail code never falls through. -/
theorem lower_tail_ne_next (hS : EntersScoped S) (n : Nat) {m : Nat} {e : Node L O P H}
    {Γ : Finset Nat} {dst next : Nat} {R N : Regs V} (hs : Scoped S.toPatterns m Γ e)
    (hΓ : ∀ i ∈ Γ, i < m) (hRN : ∀ i < m, R i = N i) (hm : m ≤ next) (R' : Regs V) :
    execN S fuses junk n (compile fuses e true dst next).1 R ≠ some (.next R') := by
  have hl := answers_fuel S fuses junk hS n (dst := dst) hs hΓ hRN hm
  intro h
  rw [h] at hl
  generalize evalN S n N e = x at hl
  cases hl

/-- Tail code declines exactly when the node executor does. -/
theorem lower_tail_none_iff (hS : EntersScoped S) (n : Nat) {m : Nat} {e : Node L O P H}
    {Γ : Finset Nat} {dst next : Nat} {R N : Regs V} (hs : Scoped S.toPatterns m Γ e)
    (hΓ : ∀ i ∈ Γ, i < m) (hRN : ∀ i < m, R i = N i) (hm : m ≤ next) :
    execN S fuses junk n (compile fuses e true dst next).1 R = none ↔ evalN S n N e = none := by
  have hl := answers_fuel S fuses junk hS n (dst := dst) hs hΓ hRN hm
  generalize execN S fuses junk n _ R = o at hl ⊢
  generalize evalN S n N e = x at hl ⊢
  cases hl <;> simp

end Fuel

/-! ## Dead registers -/

section Live
variable (S : Sem V L O P H) (ans : H → List V → Option V)

theorem agree_update {out : Finset Nat} {dst : Nat} {R₁ R₂ : Regs V} (w : Option V)
    (h : ∀ i ∈ out.erase dst, R₁ i = R₂ i) :
    ∀ i ∈ out, Function.update R₁ dst w i = Function.update R₂ dst w i := by
  intro i hi
  by_cases hid : i = dst
  · subst hid; simp
  · rw [Function.update_of_ne hid, Function.update_of_ne hid]
    exact h i (Finset.mem_erase.2 ⟨hid, hi⟩)

theorem andThen_agree {out out' : Finset Nat} {o₁ o₂ : Option (Outcome V)}
    {k₁ k₂ : Regs V → Option (Outcome V)} (h : Option.Rel (Outcome.Agree out') o₁ o₂)
    (hk : ∀ R₁ R₂, (∀ i ∈ out', R₁ i = R₂ i) →
      Option.Rel (Outcome.Agree out) (k₁ R₁) (k₂ R₂)) :
    Option.Rel (Outcome.Agree out) (andThen o₁ k₁) (andThen o₂ k₂) := by
  cases h with
  | none => exact Option.Rel.none
  | @some a b hab =>
      cases a <;> cases b <;> simp only [Outcome.Agree] at hab
      · exact hk _ _ hab
      · subst hab; exact Option.Rel.some rfl

mutual
/-- Liveness of one instruction: registers agreeing on its live-in give outcomes agreeing on its
live-out. -/
theorem step_live : ∀ (i : Instr L O P H) (out : Finset Nat) (R₁ R₂ : Regs V),
    (∀ r ∈ liveStep S.toPatterns i out, R₁ r = R₂ r) →
    Option.Rel (Outcome.Agree out) (step S ans i R₁) (step S ans i R₂)
  | .move dst src, out, R₁, R₂, h => by
      simp only [step]
      rw [read_congr S fun r hr => h r (Finset.mem_union_right _ hr)]
      cases read S R₂ src with
      | none => exact Option.Rel.none
      | some v =>
          exact Option.Rel.some (agree_update _ fun r hr => h r (Finset.mem_union_left _ hr))
  | .op dst o args, out, R₁, R₂, h => by
      simp only [step]
      rw [readAll_congr S fun r hr => h r (Finset.mem_union_right _ hr)]
      cases readAll S R₂ args with
      | none => exact Option.Rel.none
      | some vs =>
          simp only [Option.bind_some]
          cases S.op o vs with
          | none => exact Option.Rel.none
          | some v =>
              exact Option.Rel.some (agree_update _ fun r hr => h r (Finset.mem_union_left _ hr))
  | .opRet o args, out, R₁, R₂, h => by
      simp only [step]
      rw [readAll_congr S h]
      cases readAll S R₂ args with
      | none => exact Option.Rel.none
      | some vs =>
          simp only [Option.bind_some]
          cases S.op o vs with
          | none => exact Option.Rel.none
          | some v => exact Option.Rel.some rfl
  | .ite a t e, out, R₁, R₂, h => by
      simp only [step]
      rw [read_congr S fun r hr => h r (Finset.mem_union_right _ hr)]
      cases read S R₂ a with
      | none => exact Option.Rel.none
      | some v =>
          simp only [Option.bind_some]
          cases S.truth v with
          | none => exact Option.Rel.none
          | some b =>
              simp only [Option.bind_some]
              cases b
              · exact exec_live e out R₁ R₂ fun r hr =>
                  h r (Finset.mem_union_left _ (Finset.mem_union_right _ hr))
              · exact exec_live t out R₁ R₂ fun r hr =>
                  h r (Finset.mem_union_left _ (Finset.mem_union_left _ hr))
  | .iteOp o args t e, out, R₁, R₂, h => by
      simp only [step]
      rw [readAll_congr S fun r hr => h r (Finset.mem_union_right _ hr)]
      cases readAll S R₂ args with
      | none => exact Option.Rel.none
      | some vs =>
          simp only [Option.bind_some]
          cases S.op o vs with
          | none => exact Option.Rel.none
          | some v =>
              simp only [Option.bind_some]
              cases S.truth v with
              | none => exact Option.Rel.none
              | some b =>
                  simp only [Option.bind_some]
                  cases b
                  · exact exec_live e out R₁ R₂ fun r hr =>
                      h r (Finset.mem_union_left _ (Finset.mem_union_right _ hr))
                  · exact exec_live t out R₁ R₂ fun r hr =>
                      h r (Finset.mem_union_left _ (Finset.mem_union_left _ hr))
  | .bind src p, out, R₁, R₂, h => by
      simp only [step]
      rw [read_congr S fun r hr => h r (Finset.mem_union_right _ hr)]
      cases read S R₂ src with
      | none => exact Option.Rel.none
      | some v =>
          have hloc := S.bindLet_local (p := p) (v := v) (R₁ := R₁) (R₂ := R₂) fun r hr =>
            h r (Finset.mem_union_left _ (Finset.mem_union_right _ (List.mem_toFinset.2 hr)))
          simp only [Option.bind_some]
          generalize hx : S.bindLet p v R₁ = x at hloc ⊢
          generalize hy : S.bindLet p v R₂ = y at hloc ⊢
          cases hloc with
          | none => exact Option.Rel.none
          | @some R₁' R₂' hsl =>
              refine Option.Rel.some fun r hr => ?_
              by_cases hs : r ∈ S.patSlots p
              · exact hsl r hs
              · rw [S.bindLet_frame hx r hs, S.bindLet_frame hy r hs]
                exact h r (Finset.mem_union_left _ (Finset.mem_union_left _
                  (Finset.mem_sdiff.2 ⟨hr, fun h' => hs (List.mem_toFinset.1 h')⟩)))
  | .call dst h args, out, R₁, R₂, hR => by
      simp only [step]
      rw [readAll_congr S fun r hr => hR r (Finset.mem_union_right _ hr)]
      cases readAll S R₂ args with
      | none => exact Option.Rel.none
      | some vs =>
          simp only [Option.bind_some]
          cases ans h vs with
          | none => exact Option.Rel.none
          | some v =>
              exact Option.Rel.some (agree_update _ fun r hr => hR r (Finset.mem_union_left _ hr))
  | .tailCall h args, out, R₁, R₂, hR => by
      simp only [step]
      rw [readAll_congr S hR]
      cases readAll S R₂ args with
      | none => exact Option.Rel.none
      | some vs =>
          simp only [Option.bind_some]
          cases ans h vs with
          | none => exact Option.Rel.none
          | some v => exact Option.Rel.some rfl
  | .ret src, out, R₁, R₂, h => by
      simp only [step]
      rw [read_congr S h]
      cases read S R₂ src with
      | none => exact Option.Rel.none
      | some v => exact Option.Rel.some rfl
/-- **Liveness soundness.**  Register files agreeing on the live-in of `code` for live-out
`out` give outcomes that both decline, both answer the same value, or both fall through with
registers agreeing on `out`. -/
theorem exec_live : ∀ (code : List (Instr L O P H)) (out : Finset Nat) (R₁ R₂ : Regs V),
    (∀ r ∈ liveIn S.toPatterns code out, R₁ r = R₂ r) →
    Option.Rel (Outcome.Agree out) (exec S ans code R₁) (exec S ans code R₂)
  | [], _, _, _, h => Option.Rel.some h
  | i :: rest, out, R₁, R₂, h =>
      andThen_agree (step_live i (liveIn S.toPatterns rest out) R₁ R₂ h)
        fun R₁' R₂' h' => exec_live rest out R₁' R₂' h'
end

/-- **The collector at a suspended call.**  After a call's arguments are read and until its
answer is written to `dst`, the caller's registers outside `(liveIn rest out).erase dst` may be
replaced by anything (`R'`): the rest of the body runs to the same outcome. -/
theorem call_collect (dst : Nat) (h : H) (args : List (Operand L)) (rest : List (Instr L O P H))
    (out : Finset Nat) (R R' : Regs V)
    (hR' : ∀ i ∈ (liveIn S.toPatterns rest out).erase dst, R' i = R i) :
    Option.Rel (Outcome.Agree out) (exec S ans (.call dst h args :: rest) R)
      ((readAll S R args).bind fun vs => (ans h vs).bind fun v =>
        exec S ans rest (Function.update R' dst (some v))) := by
  simp only [exec, step]
  cases readAll S R args with
  | none => exact Option.Rel.none
  | some vs =>
      simp only [Option.bind_some]
      cases ans h vs with
      | none => exact Option.Rel.none
      | some v =>
          exact exec_live S ans rest out _ _ (agree_update _ fun i hi => (hR' i hi).symm)

/-- **The collector at a running call.**  Before a call reads its arguments, the registers
outside `(liveIn rest out).erase dst` and the argument registers may be replaced by anything. -/
theorem call_trim (dst : Nat) (h : H) (args : List (Operand L)) (rest : List (Instr L O P H))
    (out : Finset Nat) (R R' : Regs V)
    (hR' : ∀ i ∈ (liveIn S.toPatterns rest out).erase dst ∪ operandRegs args, R' i = R i) :
    Option.Rel (Outcome.Agree out) (exec S ans (.call dst h args :: rest) R)
      (exec S ans (.call dst h args :: rest) R') :=
  exec_live S ans _ out R R' fun i hi => (hR' i hi).symm

/-- **The collector when a call returns.**  Once the call's answer is in `dst` (`R`), the
caller's registers outside `(liveIn rest out).erase dst` and `dst` may be replaced by anything. -/
theorem call_resume (dst : Nat) (rest : List (Instr L O P H)) (out : Finset Nat) (R R' : Regs V)
    (hR' : ∀ i ∈ insert dst ((liveIn S.toPatterns rest out).erase dst), R' i = R i) :
    Option.Rel (Outcome.Agree out) (exec S ans rest R) (exec S ans rest R') := by
  refine exec_live S ans rest out R R' fun i hi => (hR' i ?_).symm
  by_cases hid : i = dst
  · exact hid ▸ Finset.mem_insert_self _ _
  · exact Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨hid, hi⟩)

/-- **The collector at a running tail call.**  Before a tail call reads its arguments, every
register but its arguments may be replaced by anything. -/
theorem tailCall_trim (h : H) (args : List (Operand L)) (rest : List (Instr L O P H))
    (out : Finset Nat) (R R' : Regs V) (hR' : ∀ i ∈ operandRegs args, R' i = R i) :
    Option.Rel (Outcome.Agree out) (exec S ans (.tailCall h args :: rest) R)
      (exec S ans (.tailCall h args :: rest) R') :=
  exec_live S ans _ out R R' fun i hi => (hR' i hi).symm

/-- **Fused compare-and-branch.**  Branching on an operation's value directly matches computing
it into a register `r` and branching on `r`, when `r` is dead in both arms. -/
theorem iteOp_fuse (o : O) (args : List (Operand L)) (t e rest : List (Instr L O P H))
    (out : Finset Nat) (r : Nat) (R : Regs V)
    (hr : r ∉ liveIn S.toPatterns t (liveIn S.toPatterns rest out) ∪
      liveIn S.toPatterns e (liveIn S.toPatterns rest out)) :
    Option.Rel (Outcome.Agree out) (exec S ans (.iteOp o args t e :: rest) R)
      (exec S ans (.op r o args :: .ite (.reg r) t e :: rest) R) := by
  have hdead : ∀ code : List (Instr L O P H),
      liveIn S.toPatterns code (liveIn S.toPatterns rest out) ⊆
      liveIn S.toPatterns t (liveIn S.toPatterns rest out) ∪
        liveIn S.toPatterns e (liveIn S.toPatterns rest out) →
      ∀ v i, i ∈ liveIn S.toPatterns code (liveIn S.toPatterns rest out) →
        R i = Function.update R r (some v) i := by
    intro code hsub v i hi
    have hne : i ≠ r := by
      rintro rfl
      exact hr (hsub hi)
    rw [Function.update_of_ne hne]
  simp only [exec, step]
  cases readAll S R args with
  | none => exact Option.Rel.none
  | some vs =>
      simp only [Option.bind_some]
      cases S.op o vs with
      | none => exact Option.Rel.none
      | some v =>
          simp only [Option.map_some, andThen, read, Function.update_self, Option.bind_some]
          cases S.truth v with
          | none => exact Option.Rel.none
          | some b =>
              cases b
              · exact andThen_agree (exec_live S ans e _ _ _
                    (hdead e Finset.subset_union_right v))
                  fun R₁ R₂ h => exec_live S ans rest out R₁ R₂ h
              · exact andThen_agree (exec_live S ans t _ _ _
                    (hdead t Finset.subset_union_left v))
                  fun R₁ R₂ h => exec_live S ans rest out R₁ R₂ h

/-- A tail call is a call into a register followed by answering that register. -/
theorem tailCall_eq (h : H) (args : List (Operand L)) (r : Nat) (rest : List (Instr L O P H))
    (R : Regs V) :
    exec S ans (.tailCall h args :: rest) R =
      exec S ans (.call r h args :: .ret (.reg r) :: rest) R := by
  simp only [exec, step]
  cases readAll S R args with
  | none => rfl
  | some vs =>
      simp only [Option.bind_some]
      cases ans h vs with
      | none => rfl
      | some v => simp [andThen, read]

/-- An operation answering for the body is the operation into any register followed by answering
that register. -/
theorem opRet_eq (o : O) (args : List (Operand L)) (r : Nat) (rest : List (Instr L O P H))
    (R : Regs V) :
    exec S ans (.opRet o args :: rest) R =
      exec S ans (.op r o args :: .ret (.reg r) :: rest) R := by
  simp only [exec, step]
  cases readAll S R args with
  | none => rfl
  | some vs =>
      simp only [Option.bind_some]
      cases S.op o vs with
      | none => rfl
      | some v => simp [andThen, read]

end Live

/-! ## Example -/

namespace Example

/-- Addition, truncated subtraction, and a comparison answering `1` or `0`. -/
inductive Op where
  | add | sub | lt
  deriving DecidableEq

/-- The one head, `tri n = n + (n - 1) + ⋯ + 1`. -/
inductive Head where
  | tri
  deriving DecidableEq

/-- The operations on naturals. -/
def op : Op → List Nat → Option Nat
  | .add, [a, b] => some (a + b)
  | .sub, [a, b] => some (a - b)
  | .lt, [a, b] => some (if a < b then 1 else 0)
  | _, _ => none

/-- `1` selects the first arm and `0` the second; no other value is a condition. -/
def truth : Nat → Option Bool
  | 0 => some false
  | 1 => some true
  | _ => none

/-- `tri`'s body, with `n` in local 0: `let m := n - 1 in if n < 1 then 0 else n + tri m`,
`m` in local 1. -/
def triBody : Node Nat Op Nat Head :=
  .bind (.op .sub [.slot 0, .lit 1]) 1
    (.ite (.op .lt [.slot 0, .lit 1]) (.lit 0) (.op .add [.slot 0, .call .tri [.slot 1]]))

/-- The example machine: a literal is its value, and let pattern `p` binds local `p`. -/
def sem : Sem Nat Nat Op Nat Head where
  patReads _ := []
  patSlots p := [p]
  lit := id
  op := op
  truth := truth
  bindLet p v R := some (Function.update R p (some v))
  bindLet_frame := by
    intro p v R R' h i hi
    cases h
    exact Function.update_of_ne (by simpa using hi) _ _
  bindLet_local := by
    intro p v R₁ R₂ _
    refine Option.Rel.some fun i hi => ?_
    simp only [List.mem_singleton] at hi
    subst hi
    simp
  enter h vs := match h, vs with
    | .tri, [n] => some ⟨triBody, 2, {0}, fun i => if i = 0 then some n else none⟩
    | _, _ => none

/-- The runtime's rule: a comparison on two operands branches directly. -/
def fuses (o : Op) (k : Nat) : Bool := o == .lt && k == 2

theorem sem_entersScoped : EntersScoped sem := by
  intro h vs e he
  cases h
  rcases vs with _ | ⟨n, _ | ⟨n', vs⟩⟩ <;> simp only [sem, reduceCtorEq] at he
  cases he
  exact ⟨by simp, by simp [Scoped, ScopedArgs, triBody, sem]⟩

/-- `tri`'s body as the lowering emits it: the comparison fused with its branch, the final
addition answering directly; registers 0 and 1 are the locals, 2 and 3 the temporaries. -/
def triCode : List (Instr Nat Op Nat Head) :=
  [.op 2 .sub [.reg 0, .lit 1], .bind (.reg 2) 1,
   .iteOp .lt [.reg 0, .lit 1] [.ret (.lit 0)]
     [.call 3 .tri [.reg 1], .opRet .add [.reg 0, .reg 3]]]

theorem compile_triBody : compile fuses triBody true 0 2 = (triCode, 4) := rfl

-- Concrete runs are checked by kernel evaluation (`decide +kernel`); the elaborator's own
-- evaluation of nested calls is far more expensive.

-- `tri 3 = 6` by the node executor, and by the register machine with 99 in every register an
-- activation's entry leaves unset.
example : nodeAnswer sem 4 .tri [3] = some 6 := by decide +kernel
example : codeAnswer sem fuses (fun _ _ _ _ => some 99) 4 .tri [3] = some 6 := by decide +kernel

-- With too little fuel both decline.
example : nodeAnswer sem 3 .tri [3] = none := by decide +kernel
example : codeAnswer sem fuses (fun _ _ _ _ => some 99) 3 .tri [3] = none := by decide +kernel

-- The theorem, for this machine: every fuel, every junk.
example (junk : Nat → Head → List Nat → Regs Nat) (n : Nat) :
    codeAnswer sem fuses junk n = nodeAnswer sem n :=
  codeAnswer_eq_nodeAnswer sem fuses sem_entersScoped junk n

-- At entry only the argument is live.
example : liveIn sem.toPatterns triCode ∅ = {0} := by decide

-- While the recursive call runs only local 0 (`n`) must be kept: `m` (local 1) and the
-- temporary 2 are dead.
example : (liveIn sem.toPatterns
    ([.opRet .add [.reg 0, .reg 3]] : List (Instr Nat Op Nat Head)) ∅).erase 3 = {0} := by
  decide

/-- The entry registers of `tri 3`. -/
def entry₃ : Regs Nat := fun i => if i = 0 then some 3 else none

-- A dead register may hold anything...
example : answer (exec sem (nodeAnswer sem 4) triCode (Function.update entry₃ 1 (some 7))) =
    some 6 := by decide +kernel
-- ...a live one may not.
example : answer (exec sem (nodeAnswer sem 5) triCode (Function.update entry₃ 0 (some 4))) =
    some 10 := by decide +kernel

/-- The value code left in register `dst` when it fell through. -/
def landed (dst : Nat) : Option (Outcome Nat) → Option Nat
  | some (.next R) => R dst
  | _ => none

/-- Registers with 5 in local 0. -/
def five : Regs Nat := fun i => if i = 0 then some 5 else none

/-- `0 + (let 1 := 1 in 2)`: the let binds a fresh local. -/
def freshLet : Node Nat Op Nat Head := .op .add [.slot 0, .bind (.lit 1) 1 (.lit 2)]

/-- `0 + (let 0 := 1 in 2)`: the let rebinds local 0, which an earlier operand reads. -/
def rebindingLet : Node Nat Op Nat Head := .op .add [.slot 0, .bind (.lit 1) 0 (.lit 2)]

example : Scoped sem.toPatterns 2 {0} freshLet := by simp [freshLet, Scoped, ScopedArgs, sem]
example : ¬ Scoped sem.toPatterns 2 {0} rebindingLet := by
  simp [rebindingLet, Scoped, ScopedArgs, sem]

-- The node executor reads local 0 before the let runs: `5 + 2` for both bodies.
example : (eval sem (nodeAnswer sem 0) five freshLet).map Prod.fst = some 7 := by decide +kernel
example : (eval sem (nodeAnswer sem 0) five rebindingLet).map Prod.fst = some 7 := by
  decide +kernel
-- The code reads local 0 when the addition consumes it, after the let: the scoped body still
-- lands `7`, the other `1 + 2`.
example : landed 2 (exec sem (nodeAnswer sem 0) (compile fuses freshLet false 2 3).1 five) =
    some 7 := by decide +kernel
example : landed 2 (exec sem (nodeAnswer sem 0) (compile fuses rebindingLet false 2 3).1 five) =
    some 3 := by decide +kernel

-- A step over a frame of two slots, `n = 2` in slot 0: `let m := n + 1 in n + tri m`, `m` in
-- slot 1.  Both executors answer `2 + 6`, and both leave `m = 3` in slot 1 for the search.
/-- The region of the example step. -/
def stepRegion : Node Nat Op Nat Head :=
  .bind (.op .add [.slot 0, .lit 1]) 1 (.op .add [.slot 0, .call .tri [.slot 1]])

/-- The example frame's slots. -/
def frame₂ : Regs Nat := fun i => if i = 0 then some 2 else none

example : (eval sem (nodeAnswer sem 5) frame₂ stepRegion).map Prod.fst = some 8 := by
  decide +kernel
example : answer (exec sem (nodeAnswer sem 5) (stepCode fuses stepRegion 2) frame₂) = some 8 := by
  decide +kernel
example : (eval sem (nodeAnswer sem 5) frame₂ stepRegion).bind (fun r => r.2 1) = some 3 := by
  decide +kernel
example : landed 1 (exec sem (nodeAnswer sem 5) (compile fuses stepRegion false 2 3).1 frame₂) =
    some 3 := by decide +kernel

-- After a call only its answer is live...
example : (liveIn sem.toPatterns ([.ret (.reg 3)] : List (Instr Nat Op Nat Head)) ∅).erase 3 =
    ∅ := by
  decide
-- ...but before the call reads its argument, clearing that argument changes the answer.
example : answer (exec sem (nodeAnswer sem 4) [.call 3 .tri [.reg 1], .ret (.reg 3)]
    (fun i => if i = 1 then some 2 else none)) = some 3 := by decide +kernel
example : answer (exec sem (nodeAnswer sem 4) [.call 3 .tri [.reg 1], .ret (.reg 3)]
    (fun _ => none)) = none := by decide +kernel

-- Fusing a comparison with its branch needs the comparison's register dead in both arms; here
-- the first arm reads it.
example : answer (exec sem (nodeAnswer sem 0)
    [.op 5 .lt [.lit 0, .lit 1], .ite (.reg 5) [.ret (.reg 5)] []] (fun _ => none)) = some 1 := by
  decide +kernel
example : answer (exec sem (nodeAnswer sem 0) [.iteOp .lt [.lit 0, .lit 1] [.ret (.reg 5)] []]
    (fun _ => none)) = none := by decide +kernel

end Example

end Mettapedia.Machines.RegisterCode
