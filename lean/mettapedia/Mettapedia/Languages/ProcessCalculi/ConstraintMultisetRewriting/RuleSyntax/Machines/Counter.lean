import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Machines.TermRewriting

/-!
# A counter machine is a finite positive program of the step, with a row for the control and a row per register

A **counter machine** with `k` registers is a list of instructions: increment a register and go on; decrement a
register and go on, or jump when it is zero; halt (`Instruction`, `Steps`). A configuration is a label and the
values of the registers.

On `RuleSyntax.step`, at the one first-order frame over rows with unknowns:

* **Rows** (`bagOf`): one control row `ctl q` for the label, and one row `reg i n` for each register, whose
  value is a term built from zero and successor (`num`).
* **The program** (`counterRules`): for an increment one rule, for a decrement two. Each takes the control row
  and the row of one register and makes them again (`incRule`, `decSuccRule`, `decZeroRule`). The program is a
  finite list of rules; no rule has a read, a tell, an equation guard, an absence check, a count check or a query
  pattern (`counterRules_fragment`). The test for zero is the pattern `reg i zero` against the pattern
  `reg i (successor x)`: positive rules suffice.
* **One machine step is one rewrite of the bag** (`rewrites_iff`), hence **one firing, and no other firing is
  admitted**, at every state that reads as the bag of the configuration (`firing_of_step`, `step_of_firing`);
  such states exist for every configuration (`Machines.exists_reads`).
* **As a correspondence** (`hosted`, `machineCorrespondence`): an `OperationalCorrespondence` from the machine
  to the step of its program, composed with `Machines.correspondence`.
* **Determinism** (`steps_deterministic`, `deterministic`): the machine has at most one step, so two admitted
  firings at a state that reads as a configuration have results that read as the same configuration.
* **Halting** (`halted_stuck`): at the control row of a label whose instruction is halt, or of a label beyond
  the program, no firing is admitted.

Cost: one firing for one machine step. A register is a unary row, as in the machine: a firing matches one
successor, and the row of a register has the size of its value. Nothing is claimed about the cost of selecting
the rows of a firing in a large store.

## Controls

* A run to its end (`transfer_runs`): the machine that moves the first register into the second, run from
  `(1, 0)`, reaches its halt label with `(0, 1)`, and the step of its program reaches a state that reads as that
  configuration.
* A jump that does not test for zero (`jumpUntested`) fires when the register is not zero, and its result is not
  the configuration the machine reaches (`jumpUntested_wrong`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Machines.Counter

open Mettapedia.Logic.LP
open Mettapedia.GSLT
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis (equalityGSLT)
open NamesOnTheStep (Expr)
open Presentation.Schematic

/-! ## The machine -/

/-- **An instruction of a counter machine** with `k` registers. -/
inductive Instruction (k : ℕ) where
  | inc (register : Fin k) (next : ℕ)
  | dec (register : Fin k) (next jump : ℕ)
  | halt

/-- **A configuration**: a label and the values of the registers. -/
structure Config (k : ℕ) where
  label : ℕ
  registers : Fin k → ℕ

variable {k : ℕ}

/-- The instruction at a label; beyond the end of the program, halt. -/
def instructionAt : List (Instruction k) → ℕ → Instruction k
  | [], _ => .halt
  | i :: _, 0 => i
  | _ :: program, q + 1 => instructionAt program q

/-- **One step of a counter machine.** -/
inductive Steps (program : List (Instruction k)) : Config k → Config k → Prop
  | inc (c : Config k) (r : Fin k) (next : ℕ) (fetched : instructionAt program c.label = .inc r next) :
      Steps program c ⟨next, Function.update c.registers r (c.registers r + 1)⟩
  | decZero (c : Config k) (r : Fin k) (next jump : ℕ)
      (fetched : instructionAt program c.label = .dec r next jump) (empty : c.registers r = 0) :
      Steps program c ⟨jump, c.registers⟩
  | decSucc (c : Config k) (r : Fin k) (next jump n : ℕ)
      (fetched : instructionAt program c.label = .dec r next jump) (positive : c.registers r = n + 1) :
      Steps program c ⟨next, Function.update c.registers r n⟩

theorem label_lt_of_ne_halt : ∀ (program : List (Instruction k)) (q : ℕ),
    instructionAt program q ≠ .halt → q < program.length
  | [], _, notHalt => absurd rfl notHalt
  | _ :: _, 0, _ => Nat.succ_pos _
  | _ :: program, q + 1, notHalt => Nat.succ_lt_succ (label_lt_of_ne_halt program q notHalt)

/-- **A machine has at most one step.** -/
theorem steps_deterministic {program : List (Instruction k)} {c c₁ c₂ : Config k}
    (first : Steps program c c₁) (second : Steps program c c₂) : c₁ = c₂ := by
  cases first with
  | inc r next fetched =>
      cases second with
      | inc r' next' fetched' =>
          cases fetched.symm.trans fetched'
          rfl
      | decZero r' next' jump' fetched' _ => cases fetched.symm.trans fetched'
      | decSucc r' next' jump' n' fetched' _ => cases fetched.symm.trans fetched'
  | decZero r next jump fetched empty =>
      cases second with
      | inc r' next' fetched' => cases fetched.symm.trans fetched'
      | decZero r' next' jump' fetched' _ =>
          cases fetched.symm.trans fetched'
          rfl
      | decSucc r' next' jump' n' fetched' positive' =>
          cases fetched.symm.trans fetched'
          omega
  | decSucc r next jump n fetched positive =>
      cases second with
      | inc r' next' fetched' => cases fetched.symm.trans fetched'
      | decZero r' next' jump' fetched' empty' =>
          cases fetched.symm.trans fetched'
          omega
      | decSucc r' next' jump' n' fetched' positive' =>
          cases fetched.symm.trans fetched'
          have same : n = n' := by omega
          rw [same]

theorem no_step_of_halt {program : List (Instruction k)} {c c' : Config k}
    (halted : instructionAt program c.label = .halt) : ¬ Steps program c c' := by
  intro stepped
  cases stepped with
  | inc r next fetched => cases halted.symm.trans fetched
  | decZero r next jump fetched _ => cases halted.symm.trans fetched
  | decSucc r next jump n fetched _ => cases halted.symm.trans fetched

/-! ## Rows -/

/-- A number as a row: zero, and successor. -/
def num : ℕ → Expr
  | 0 => .name 2
  | n + 1 => .code (num n)

/-- The control row of a label. -/
def ctl (q : ℕ) : Expr := .app (.name 0) (.sym q)

/-- The row of a register with its value. -/
def reg (i : Fin k) (value : Expr) : Expr := .app (.app (.name 1) (.sym i.val)) value

theorem num_injective : ∀ {m n : ℕ}, num m = num n → m = n
  | 0, 0, _ => rfl
  | 0, _ + 1, same => by cases same
  | _ + 1, 0, same => by cases same
  | _ + 1, _ + 1, same => congrArg Nat.succ (num_injective (Expr.code.inj same))

theorem zero_eq_num : ∀ {m : ℕ}, Expr.name 2 = num m → m = 0
  | 0, _ => rfl
  | _ + 1, same => by cases same

theorem code_eq_num : ∀ {t : Expr} {m : ℕ}, Expr.code t = num m → ∃ n, m = n + 1 ∧ t = num n
  | _, 0, same => by cases same
  | _, n + 1, same => ⟨n, rfl, Expr.code.inj same⟩

theorem ctl_injective {q q' : ℕ} (same : ctl q = ctl q') : q = q' :=
  Expr.sym.inj (Expr.app.inj same).2

theorem ctl_ne_reg (q : ℕ) (i : Fin k) (value : Expr) : ctl q ≠ reg i value := by
  intro same
  cases (Expr.app.inj same).1

theorem reg_injective {i j : Fin k} {v w : Expr} (same : reg i v = reg j w) : i = j ∧ v = w :=
  ⟨Fin.ext (Expr.sym.inj (Expr.app.inj (Expr.app.inj same).1).2), (Expr.app.inj same).2⟩

/-- The rows of the registers other than one. -/
def others (registers : Fin k → ℕ) (r : Fin k) : Multiset Expr :=
  (Finset.univ.erase r).val.map fun j => reg j (num (registers j))

/-- **The bag of a configuration**: its control row and one row per register. -/
def bagOf (c : Config k) : Multiset Expr :=
  ctl c.label ::ₘ Finset.univ.val.map fun j => reg j (num (c.registers j))

/-- The bag of a configuration: its control row, the row of one register, and the other registers. -/
theorem bagOf_split (c : Config k) (r : Fin k) :
    bagOf c = ctl c.label ::ₘ reg r (num (c.registers r)) ::ₘ others c.registers r := by
  unfold bagOf others
  rw [Finset.erase_val, ← Multiset.map_cons (fun j => reg j (num (c.registers j))),
    Multiset.cons_erase (Finset.mem_univ_val r)]

theorem others_update (registers : Fin k → ℕ) (r : Fin k) (v : ℕ) :
    others (Function.update registers r v) r = others registers r := by
  unfold others
  refine Multiset.map_congr rfl fun j member => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase (Finset.mem_val.mp member))]

theorem bagOf_update (q : ℕ) (registers : Fin k → ℕ) (r : Fin k) (v : ℕ) :
    bagOf ⟨q, Function.update registers r v⟩ = ctl q ::ₘ reg r (num v) ::ₘ others registers r := by
  rw [bagOf_split ⟨q, Function.update registers r v⟩ r]
  show ctl q ::ₘ reg r (num (Function.update registers r v r)) ::ₘ
    others (Function.update registers r v) r = _
  rw [Function.update_self, others_update]

theorem mem_bagOf {c : Config k} {x : Expr} (inside : x ∈ bagOf c) :
    x = ctl c.label ∨ ∃ j : Fin k, x = reg j (num (c.registers j)) := by
  rcases Multiset.mem_cons.mp inside with same | inRegisters
  · exact Or.inl same
  · obtain ⟨j, -, rfl⟩ := Multiset.mem_map.mp inRegisters
    exact Or.inr ⟨j, rfl⟩

theorem label_of_ctl_mem {c : Config k} {q : ℕ} (inside : ctl q ∈ bagOf c) : q = c.label := by
  rcases mem_bagOf inside with same | ⟨j, same⟩
  · exact ctl_injective same
  · exact absurd same (ctl_ne_reg q j _)

theorem value_of_reg_mem {c : Config k} {r : Fin k} {v : Expr} (inside : reg r v ∈ bagOf c) :
    v = num (c.registers r) := by
  rcases mem_bagOf inside with same | ⟨j, same⟩
  · exact absurd same.symm (ctl_ne_reg _ r v)
  · obtain ⟨rfl, value⟩ := reg_injective same
    exact value

/-- Two rows beside a rest. -/
theorem pair_add (a b : Expr) (rest : Multiset Expr) :
    (([a, b] : List Expr) : Multiset Expr) + rest = a ::ₘ b ::ₘ rest := by
  rw [← Multiset.cons_coe, ← Multiset.cons_coe, Multiset.cons_add, Multiset.cons_add, Multiset.coe_nil,
    zero_add]

/-- The rest beside the control row and a register row of a configuration is its other registers. -/
theorem rest_of_split {c : Config k} {r : Fin k} {rest : Multiset Expr}
    (split : ctl c.label ::ₘ reg r (num (c.registers r)) ::ₘ rest = bagOf c) :
    rest = others c.registers r := by
  rw [bagOf_split c r] at split
  exact (Multiset.cons_inj_right _).mp ((Multiset.cons_inj_right _).mp split)

/-! ## The rules -/

/-- A constant, as a pattern. -/
def sy (j : ℕ) : Tm := .const (.sym j)

/-- A name, as a pattern. -/
def nm (j : ℕ) : Tm := .const (.name j)

/-- An unknown of a rule. -/
def un (x : ℕ) : Tm := .var x

/-- An application, as a pattern. -/
def apT (f a : Tm) : Tm := .app .app (args2 f a)

/-- A successor, as a pattern. -/
def sc (t : Tm) : Tm := .app .code (args1 t)

/-- The pattern of the control row of a label. -/
def ctlP (q : ℕ) : Tm := apT (nm 0) (sy q)

/-- The pattern of the row of a register. -/
def regP (i : Fin k) (value : Tm) : Tm := apT (apT (nm 1) (sy i.val)) value

/-- **A rule that takes two rows and makes two rows.** -/
def twoRule (l₁ l₂ r₁ r₂ : Tm) : SRule := ⟨PUnit.unit, ⟨[l₁, l₂], [], [], [], [r₁, r₂]⟩, []⟩

/-- A two-row rule whose made rows have only unknowns of its taken rows is range-restricted and positive. -/
theorem twoRule_fragment {l₁ l₂ r₁ r₂ : Tm}
    (range : ∀ x, x ∈ unknowns r₁ ++ unknowns r₂ → x ∈ unknowns l₁ ++ unknowns l₂) :
    RangeRestrictedPositive (twoRule l₁ l₂ r₁ r₂) := by
  refine ⟨rfl, rfl, fun t inWritten x vars => ?_⟩
  have inMade : t = r₁ ∨ t = r₂ := by simpa [written, twoRule] using inWritten
  have inRight : x ∈ unknowns r₁ ++ unknowns r₂ := by
    rcases inMade with isFirst | isSecond
    · rw [isFirst] at vars
      exact List.mem_append_left _ (mem_unknowns r₁ vars)
    · rw [isSecond] at vars
      exact List.mem_append_right _ (mem_unknowns r₂ vars)
  rcases List.mem_append.mp (range x inRight) with inLeft | inLeft
  · exact ⟨l₁, List.mem_cons_self, vars_of_mem_unknowns l₁ inLeft⟩
  · exact ⟨l₂, List.mem_cons_of_mem _ List.mem_cons_self, vars_of_mem_unknowns l₂ inLeft⟩

/-- **Increment**: at the label, the register's value becomes its successor. -/
def incRule (q : ℕ) (i : Fin k) (next : ℕ) : SRule :=
  twoRule (ctlP q) (regP i (un 0)) (ctlP next) (regP i (sc (un 0)))

/-- **Decrement**: at the label, a successor value becomes its predecessor. -/
def decSuccRule (q : ℕ) (i : Fin k) (next : ℕ) : SRule :=
  twoRule (ctlP q) (regP i (sc (un 0))) (ctlP next) (regP i (un 0))

/-- **Jump when zero**: at the label, a zero value stays and the control jumps. -/
def decZeroRule (q : ℕ) (i : Fin k) (jump : ℕ) : SRule :=
  twoRule (ctlP q) (regP i (nm 2)) (ctlP jump) (regP i (nm 2))

/-- The rules of an instruction at a label. -/
def rulesAt (q : ℕ) : Instruction k → List SRule
  | .inc i next => [incRule q i next]
  | .dec i next jump => [decSuccRule q i next, decZeroRule q i jump]
  | .halt => []

/-- **The program of a counter machine**: the rules of its instructions at their labels. -/
def counterRules (program : List (Instruction k)) : List SRule :=
  (List.range program.length).flatMap fun q => rulesAt q (instructionAt program q)

/-- **The program of a counter machine is range-restricted and positive**: its rules have no read, tell or
check. -/
theorem counterRules_fragment (program : List (Instruction k)) :
    ∀ r ∈ counterRules program, RangeRestrictedPositive r := by
  intro r member
  obtain ⟨q, -, inAt⟩ := List.mem_flatMap.mp member
  cases fetched : instructionAt program q with
  | inc i next =>
      rw [fetched] at inAt
      rw [List.mem_singleton.mp inAt]
      exact twoRule_fragment fun _ inside => inside
  | dec i next jump =>
      rw [fetched] at inAt
      rcases List.mem_cons.mp inAt with isSucc | inAt
      · rw [isSucc]
        exact twoRule_fragment fun _ inside => inside
      · rw [List.mem_singleton.mp inAt]
        exact twoRule_fragment fun _ inside => inside
  | halt =>
      rw [fetched] at inAt
      exact absurd inAt List.not_mem_nil

/-! ## One rule on the bag of a configuration -/

/-- **The increment rule on the bag of a configuration**: it rewrites exactly at its label, to the bag of the
configuration with the register incremented. -/
theorem rewrites_inc_iff (c : Config k) (q : ℕ) (i : Fin k) (next : ℕ) (bag' : Multiset Expr) :
    Rewrites [incRule q i next] (bagOf c) bag' ↔
      q = c.label ∧ bag' = bagOf ⟨next, Function.update c.registers i (c.registers i + 1)⟩ := by
  constructor
  · rintro ⟨r, member, θ, rest, split, -, -, rfl⟩
    obtain rfl := List.mem_singleton.mp member
    have split' : ctl q ::ₘ reg i (θ 0) ::ₘ rest = bagOf c := (pair_add _ _ rest).symm.trans split
    have atLabel : q = c.label := label_of_ctl_mem (by
      rw [← split']
      exact Multiset.mem_cons_self _ _)
    have value : θ 0 = num (c.registers i) := value_of_reg_mem (by
      rw [← split']
      exact Multiset.mem_cons_of_mem (Multiset.mem_cons_self _ _))
    rw [atLabel, value] at split'
    have restIs := rest_of_split split'
    refine ⟨atLabel, ?_⟩
    rw [bagOf_update, ← restIs]
    show _ = ctl next ::ₘ reg i (Expr.code (num (c.registers i))) ::ₘ rest
    rw [← value]
    exact pair_add _ _ rest
  · rintro ⟨rfl, rfl⟩
    exact ⟨incRule c.label i next, List.mem_singleton_self _, fun _ => num (c.registers i),
      others c.registers i, (pair_add _ _ _).trans (bagOf_split c i).symm,
      fun q member => absurd member List.not_mem_nil, fun e member => absurd member List.not_mem_nil,
      (bagOf_update next c.registers i _).trans (pair_add _ _ _).symm⟩

/-- **The decrement rule on the bag of a configuration**: it rewrites exactly at its label and at a successor
value, to the bag of the configuration with the register decremented. -/
theorem rewrites_decSucc_iff (c : Config k) (q : ℕ) (i : Fin k) (next : ℕ) (bag' : Multiset Expr) :
    Rewrites [decSuccRule q i next] (bagOf c) bag' ↔
      q = c.label ∧ ∃ n, c.registers i = n + 1 ∧ bag' = bagOf ⟨next, Function.update c.registers i n⟩ := by
  constructor
  · rintro ⟨r, member, θ, rest, split, -, -, rfl⟩
    obtain rfl := List.mem_singleton.mp member
    have split' : ctl q ::ₘ reg i (Expr.code (θ 0)) ::ₘ rest = bagOf c :=
      (pair_add _ _ rest).symm.trans split
    have atLabel : q = c.label := label_of_ctl_mem (by
      rw [← split']
      exact Multiset.mem_cons_self _ _)
    have value : Expr.code (θ 0) = num (c.registers i) := value_of_reg_mem (by
      rw [← split']
      exact Multiset.mem_cons_of_mem (Multiset.mem_cons_self _ _))
    obtain ⟨n, positive, isNum⟩ := code_eq_num value
    rw [atLabel, value] at split'
    have restIs := rest_of_split split'
    refine ⟨atLabel, n, positive, ?_⟩
    rw [bagOf_update, ← restIs, ← isNum]
    exact pair_add _ _ rest
  · rintro ⟨rfl, n, positive, rfl⟩
    refine ⟨decSuccRule c.label i next, List.mem_singleton_self _, fun _ => num n, others c.registers i, ?_,
      fun q member => absurd member List.not_mem_nil, fun e member => absurd member List.not_mem_nil,
      (bagOf_update next c.registers i n).trans (pair_add _ _ _).symm⟩
    rw [bagOf_split c i, positive]
    exact pair_add _ _ _

/-- **The jump rule on the bag of a configuration**: it rewrites exactly at its label and at a zero value, to
the bag of the configuration at the jump label. -/
theorem rewrites_decZero_iff (c : Config k) (q : ℕ) (i : Fin k) (jump : ℕ) (bag' : Multiset Expr) :
    Rewrites [decZeroRule q i jump] (bagOf c) bag' ↔
      q = c.label ∧ c.registers i = 0 ∧ bag' = bagOf ⟨jump, c.registers⟩ := by
  constructor
  · rintro ⟨r, member, θ, rest, split, -, -, rfl⟩
    obtain rfl := List.mem_singleton.mp member
    have split' : ctl q ::ₘ reg i (Expr.name 2) ::ₘ rest = bagOf c := (pair_add _ _ rest).symm.trans split
    have atLabel : q = c.label := label_of_ctl_mem (by
      rw [← split']
      exact Multiset.mem_cons_self _ _)
    have value : Expr.name 2 = num (c.registers i) := value_of_reg_mem (by
      rw [← split']
      exact Multiset.mem_cons_of_mem (Multiset.mem_cons_self _ _))
    have empty : c.registers i = 0 := zero_eq_num value
    rw [atLabel] at split'
    have restIs : rest = others c.registers i := rest_of_split (c := c) (r := i) (rest := rest) (by
      rw [empty]
      exact split')
    refine ⟨atLabel, empty, ?_⟩
    rw [bagOf_split ⟨jump, c.registers⟩ i]
    show _ = ctl jump ::ₘ reg i (num (c.registers i)) ::ₘ others c.registers i
    rw [← restIs, empty]
    exact pair_add _ _ rest
  · rintro ⟨rfl, empty, rfl⟩
    refine ⟨decZeroRule c.label i jump, List.mem_singleton_self _, fun _ => .sym 0, others c.registers i, ?_,
      fun q member => absurd member List.not_mem_nil, fun e member => absurd member List.not_mem_nil, ?_⟩
    · rw [bagOf_split c i, empty]
      exact pair_add _ _ _
    · rw [bagOf_split ⟨jump, c.registers⟩ i]
      show ctl jump ::ₘ reg i (num (c.registers i)) ::ₘ others c.registers i = _
      rw [empty]
      exact (pair_add _ _ _).symm

/-! ## One machine step is one rewrite of the bag -/

theorem mem_counterRules {program : List (Instruction k)} {q : ℕ} {r : SRule}
    (running : instructionAt program q ≠ .halt) (inAt : r ∈ rulesAt q (instructionAt program q)) :
    r ∈ counterRules program :=
  List.mem_flatMap.mpr ⟨q, List.mem_range.mpr (label_lt_of_ne_halt program q running), inAt⟩

/-- **One step of a counter machine is one rewrite of the bag of its configuration, and every rewrite of that
bag by the program is the step.** -/
theorem rewrites_iff (program : List (Instruction k)) (c : Config k) (bag' : Multiset Expr) :
    Rewrites (counterRules program) (bagOf c) bag' ↔ ∃ c', Steps program c c' ∧ bag' = bagOf c' := by
  constructor
  · rintro ⟨r, member, θ, rest, split, readsIn, equations, made⟩
    have single : Rewrites [r] (bagOf c) bag' :=
      ⟨r, List.mem_singleton_self r, θ, rest, split, readsIn, equations, made⟩
    obtain ⟨q, -, inAt⟩ := List.mem_flatMap.mp member
    cases fetched : instructionAt program q with
    | inc i next =>
        rw [fetched] at inAt
        rw [List.mem_singleton.mp inAt] at single
        obtain ⟨atLabel, isBag⟩ := (rewrites_inc_iff c q i next bag').mp single
        rw [atLabel] at fetched
        exact ⟨_, Steps.inc c i next fetched, isBag⟩
    | dec i next jump =>
        rw [fetched] at inAt
        rcases List.mem_cons.mp inAt with isSucc | inAt
        · rw [isSucc] at single
          obtain ⟨atLabel, n, positive, isBag⟩ := (rewrites_decSucc_iff c q i next bag').mp single
          rw [atLabel] at fetched
          exact ⟨_, Steps.decSucc c i next jump n fetched positive, isBag⟩
        · rw [List.mem_singleton.mp inAt] at single
          obtain ⟨atLabel, empty, isBag⟩ := (rewrites_decZero_iff c q i jump bag').mp single
          rw [atLabel] at fetched
          exact ⟨_, Steps.decZero c i next jump fetched empty, isBag⟩
    | halt =>
        rw [fetched] at inAt
        exact absurd inAt List.not_mem_nil
  · rintro ⟨c', stepped, rfl⟩
    cases stepped with
    | inc r next fetched =>
        refine rewrites_of_mem (mem_counterRules (q := c.label) ?_ ?_)
          ((rewrites_inc_iff c c.label r next _).mpr ⟨rfl, rfl⟩)
        · rw [fetched]
          intro impossible
          cases impossible
        · rw [fetched]
          exact List.mem_singleton_self _
    | decZero r next jump fetched empty =>
        refine rewrites_of_mem (mem_counterRules (q := c.label) ?_ ?_)
          ((rewrites_decZero_iff c c.label r jump _).mpr ⟨rfl, empty, rfl⟩)
        · rw [fetched]
          intro impossible
          cases impossible
        · rw [fetched]
          exact List.mem_cons_of_mem _ (List.mem_singleton_self _)
    | decSucc r next jump n fetched positive =>
        refine rewrites_of_mem (mem_counterRules (q := c.label) ?_ ?_)
          ((rewrites_decSucc_iff c c.label r next _).mpr ⟨rfl, n, positive, rfl⟩)
        · rw [fetched]
          intro impossible
          cases impossible
        · rw [fetched]
          exact List.mem_cons_self

/-! ## One machine step is one firing -/

/-- **A step of the machine is one admitted firing of its program**, at every state that reads as the bag of
the configuration, and the result reads as the bag of the next configuration. -/
theorem firing_of_step (program : List (Instruction k)) {c c' : Config k} {s : SState ℕ}
    (reads : ReadsBag s (bagOf c)) (stepped : Steps program c c') :
    ∃ (g : Firing ℕ E {r | r ∈ counterRules program} s.frame)
      (admitted : (schematicStep ℕ (counterRules program)).Admits (s := s) g),
      ReadsBag ((schematicStep ℕ (counterRules program)).result g admitted) (bagOf c') :=
  readsBag_forward (counterRules_fragment program) reads
    ((rewrites_iff program c _).mpr ⟨c', stepped, rfl⟩)

/-- **Every admitted firing of the program is the step of the machine**: at a state that reads as the bag of
a configuration, the result of an admitted firing reads as the bag of a configuration the machine steps to. -/
theorem step_of_firing (program : List (Instruction k)) {c : Config k} {s : SState ℕ}
    (reads : ReadsBag s (bagOf c)) (g : Firing ℕ E {r | r ∈ counterRules program} s.frame)
    (admitted : (schematicStep ℕ (counterRules program)).Admits (s := s) g) :
    ∃ c', Steps program c c' ∧
      ReadsBag ((schematicStep ℕ (counterRules program)).result g admitted) (bagOf c') := by
  obtain ⟨bag', rewrites, reads'⟩ := readsBag_backward (counterRules_fragment program) reads g admitted
  obtain ⟨c', stepped, rfl⟩ := (rewrites_iff program c bag').mp rewrites
  exact ⟨c', stepped, reads'⟩

/-- **The runs are determined up to the made identities and the openings**: two admitted firings at a state
that reads as a configuration have results that read as one and the same configuration. -/
theorem deterministic (program : List (Instruction k)) {c : Config k} {s : SState ℕ}
    (reads : ReadsBag s (bagOf c)) (g g' : Firing ℕ E {r | r ∈ counterRules program} s.frame)
    (admitted : (schematicStep ℕ (counterRules program)).Admits (s := s) g)
    (admitted' : (schematicStep ℕ (counterRules program)).Admits (s := s) g') :
    ∃ c' : Config k, ReadsBag ((schematicStep ℕ (counterRules program)).result g admitted) (bagOf c') ∧
      ReadsBag ((schematicStep ℕ (counterRules program)).result g' admitted') (bagOf c') := by
  obtain ⟨c₁, first, reads₁⟩ := step_of_firing program reads g admitted
  obtain ⟨c₂, second, reads₂⟩ := step_of_firing program reads g' admitted'
  rw [← steps_deterministic first second] at reads₂
  exact ⟨c₁, reads₁, reads₂⟩

/-- **At a halt label no firing is admitted.** -/
theorem halted_stuck (program : List (Instruction k)) {c : Config k} {s : SState ℕ}
    (reads : ReadsBag s (bagOf c)) (halted : instructionAt program c.label = .halt)
    (g : Firing ℕ E {r | r ∈ counterRules program} s.frame) :
    ¬ (schematicStep ℕ (counterRules program)).Admits (s := s) g := by
  intro admitted
  obtain ⟨c', stepped, -⟩ := step_of_firing program reads g admitted
  exact no_step_of_halt halted stepped

/-! ## The correspondence -/

/-- **A counter machine, as a system**: configurations under its step. -/
def machine (program : List (Instruction k)) : GSLT := equalityGSLT (Config k) (Steps program)

/-- A configuration is hosted by its bag. -/
def BagOf (c : Config k) (bag : Multiset Expr) : Prop := bag = bagOf c

/-- **A counter machine and rewriting of the bags of its configurations**: one step for one rewrite, both
ways. -/
def hosted (program : List (Instruction k)) :
    OperationalCorrespondence (machine program) (rewriting (counterRules program)) where
  related := BagOf
  readStep := by
    intro c bag bag' same stepped
    have isBag : bag = bagOf c := same
    subst isBag
    obtain ⟨c', advanced, sameBag⟩ := (rewrites_iff program c bag').mp stepped
    exact Or.inr ⟨c', advanced, sameBag⟩
  forward := by
    intro c c' bag same stepped
    have isBag : bag = bagOf c := same
    subst isBag
    exact ⟨bagOf c', (executionPath_nonempty_iff_multiStep (rewriting (counterRules program)) _ _).mpr
      (.step ((rewrites_iff program c _).mpr ⟨c', stepped, rfl⟩) (.refl _)), rfl⟩

/-- **A counter machine and the step of its program**: one machine step for one firing, both ways, related by
reading a state as the bag of the configuration. -/
def machineCorrespondence (program : List (Instruction k)) :
    OperationalCorrespondence (machine program) (stepSystem ℕ (counterRules program)) :=
  (hosted program).comp (correspondence (O := ℕ) (counterRules_fragment program))

/-! ## Controls -/

/-- The machine that moves the first register into the second: decrement the first or jump to the end;
increment the second and go back; halt. -/
def transfer : List (Instruction 2) := [.dec 0 1 2, .inc 1 0, .halt]

/-- The configuration after the three steps of the transfer machine from `(1, 0)`. -/
def transferred : Config 2 :=
  ⟨2, Function.update (Function.update ![1, 0] 0 0) 1 (Function.update ![1, 0] 0 0 1 + 1)⟩

theorem transfer_steps : (machine transfer).MultiStep ⟨0, ![1, 0]⟩ transferred :=
  .step (Steps.decSucc (program := transfer) (⟨0, ![1, 0]⟩ : Config 2) 0 1 2 0 rfl rfl)
    (.step (Steps.inc (program := transfer) (⟨1, Function.update ![1, 0] 0 0⟩ : Config 2) 1 0 rfl)
      (.step (Steps.decZero (program := transfer) (⟨0, Function.update (Function.update ![1, 0] 0 0) 1
        (Function.update ![1, 0] 0 0 1 + 1)⟩ : Config 2) 0 1 2 rfl rfl) (.refl _)))

/-- **A run to its end**: the transfer machine from `(1, 0)` reaches its halt label with `(0, 1)`, and from a
state that reads as the start configuration the step of its program reaches a state that reads as that
configuration. -/
theorem transfer_runs :
    instructionAt transfer transferred.label = .halt ∧ transferred.registers 0 = 0 ∧
      transferred.registers 1 = 1 ∧
      ∃ s s' : SState ℕ, ReadsBag s (bagOf (⟨0, ![1, 0]⟩ : Config 2)) ∧
        (stepSystem ℕ (counterRules transfer)).MultiStep s s' ∧ ReadsBag s' (bagOf transferred) := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  obtain ⟨s, reads⟩ := exists_reads (bagOf (⟨0, ![1, 0]⟩ : Config 2))
  obtain ⟨s', path, bag, isBag, reads'⟩ :=
    (machineCorrespondence transfer).liftMultiStep ⟨_, rfl, reads⟩ transfer_steps
  have same : bag = bagOf transferred := isBag
  rw [same] at reads'
  exact ⟨s, s', reads, path, reads'⟩

/-- A jump that does not test the register for zero. -/
def jumpUntested (q : ℕ) (i : Fin k) (jump : ℕ) : SRule :=
  twoRule (ctlP q) (regP i (un 0)) (ctlP jump) (regP i (un 0))

/-- **The untested jump fires when the register is not zero, and its result is not the configuration the
machine reaches**: the test for zero is needed, and it is a pattern. -/
theorem jumpUntested_wrong (c : Config k) (i : Fin k) (next jump n : ℕ) (positive : c.registers i = n + 1) :
    Rewrites [jumpUntested c.label i jump] (bagOf c) (bagOf ⟨jump, c.registers⟩) ∧
      bagOf (⟨jump, c.registers⟩ : Config k) ≠ bagOf ⟨next, Function.update c.registers i n⟩ := by
  refine ⟨⟨jumpUntested c.label i jump, List.mem_singleton_self _, fun _ => num (c.registers i),
    others c.registers i, (pair_add _ _ _).trans (bagOf_split c i).symm,
    fun q member => absurd member List.not_mem_nil, fun e member => absurd member List.not_mem_nil,
    (bagOf_split ⟨jump, c.registers⟩ i).trans (pair_add _ _ _).symm⟩, fun same => ?_⟩
  have inside : reg i (num (c.registers i)) ∈ bagOf (⟨jump, c.registers⟩ : Config k) := by
    rw [bagOf_split ⟨jump, c.registers⟩ i]
    exact Multiset.mem_cons_of_mem (Multiset.mem_cons_self _ _)
  rw [same] at inside
  have value : num (c.registers i) = num (Function.update c.registers i n i) := value_of_reg_mem inside
  rw [Function.update_self] at value
  have equal := num_injective value
  omega

#print axioms steps_deterministic
#print axioms counterRules_fragment
#print axioms rewrites_iff
#print axioms firing_of_step
#print axioms step_of_firing
#print axioms deterministic
#print axioms halted_stuck
#print axioms hosted
#print axioms machineCorrespondence
#print axioms transfer_runs
#print axioms jumpUntested_wrong

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Machines.Counter
