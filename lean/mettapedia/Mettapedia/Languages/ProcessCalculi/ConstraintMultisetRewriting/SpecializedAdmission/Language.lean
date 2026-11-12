import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SpecializedAdmission.Terms

/-!
# The decision language of specialized admission

A program decides the firings of one rule on first-order states of the ground fragment. It is
straight-line code over registers that hold run-time terms, in the manner of a WAM compiler's
output, with exits that refuse for a reason:

* **loads** (`loadParam`, `loadConst`, `loadFresh`, `mkApp`, `lookup`) write one register;
* **shape tests** (`needName`, `paramMinted`, `occNonzero`, `occDistinct`) read the frame and the
  selected identities;
* **match instructions** (`MInstr`: `getApp`, `eqReg`, `eqConst`, `eqFresh`) test a run-time term
  against the rule and load its arguments; `test` runs one and refuses on failure;
* **guard instructions**: `countEq` counts the present labels equal to a register; `scanNone`
  refuses when some present label passes a matching body (a pattern with guard-only locals);
* **commits** (`remove`, `mint`, `add`) change the state: they take an occurrence, mint names,
  and make an occurrence with the next identity.

A program is a check part and a commit part (`Prog`). `Prog.admits` runs the checks (admission
alone); `Prog.fire` runs the checks and, on admission, the commit part. A refusal stops the run
where it happens: whatever ran before it stays done (`run`), so "a refusal changes nothing" is a
property of a program, not of the language (`run_pure`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SpecializedAdmission

/-- Why a firing is refused: the first conjunct of admission that fails, and for a guard, which
guard. -/
inductive Reason where
  | shapes
  | fits
  | unsolvable
  | guard (i : Nat)
  deriving DecidableEq

/-- A present occurrence: its identity and its label. -/
structure Row where
  id : Nat
  label : Tm
  deriving DecidableEq

/-- A first-order state: its frame (declared variables, live disequations, minted names), the
next occurrence identity, and the present occurrences in the order they were made. -/
structure St where
  vars : Nat
  diseqs : Nat
  names : Nat
  nextId : Nat
  present : List Row
  deriving DecidableEq

/-- The label of the occurrence with identity `id`, when it is present. -/
def labelOf (s : St) (id : Nat) : Option Tm :=
  (s.present.find? fun row => row.id == id).map Row.label

/-- Registers: run-time terms by number. -/
abbrev Regs := Nat → Tm

def Regs.write (rs : Regs) (r : Nat) (v : Tm) : Regs := fun i => if i = r then v else rs i

/-- `vs` written into the registers `d`, `d + 1`, .... -/
def Regs.writeList (rs : Regs) (d : Nat) : List Tm → Regs
  | [] => rs
  | v :: vs => Regs.writeList (rs.write d v) (d + 1) vs

/-- Match instructions: a test of a run-time term against the rule. -/
inductive MInstr where
  /-- register `src` holds `app f vs` with `len` arguments; `vs` go to `dst`, `dst + 1`, ... -/
  | getApp (src f len dst : Nat)
  /-- registers `a` and `b` hold the same term -/
  | eqReg (a b : Nat)
  /-- register `a` holds the closed term `t` -/
  | eqConst (a : Nat) (t : Tm)
  /-- register `a` holds the `j`-th name the firing mints -/
  | eqFresh (a j : Nat)

def MInstr.exec (names : Nat) (rs : Regs) : MInstr → Option Regs
  | .getApp src f len dst => match rs src with
      | .app g vs => if g = f ∧ vs.length = len then some (rs.writeList dst vs) else none
      | _ => none
  | .eqReg a b => if rs a = rs b then some rs else none
  | .eqConst a t => if rs a = t then some rs else none
  | .eqFresh a j => if rs a = .name (names + j) then some rs else none

def MInstr.run (names : Nat) : List MInstr → Regs → Option Regs
  | [], rs => some rs
  | i :: is, rs => match i.exec names rs with
      | some rs' => MInstr.run names is rs'
      | none => none

/-- Instructions. -/
inductive Instr where
  | loadParam (dst k : Nat)
  | loadConst (dst : Nat) (t : Tm)
  | loadFresh (dst j : Nat)
  | mkApp (dst f : Nat) (args : List Nat)
  /-- shapes: the frame has minted the name `k` -/
  | needName (k : Nat)
  /-- shapes: every name of parameter `k` is minted -/
  | paramMinted (k : Nat)
  /-- shapes: the identity of use `u` is not `0` -/
  | occNonzero (u : Nat)
  /-- the identities of uses `u` and `v` differ, or refuse for `why` -/
  | occDistinct (u v : Nat) (why : Reason)
  /-- fits: the occurrence of use `u` is present; its label goes to `dst` -/
  | lookup (u dst : Nat)
  | test (m : MInstr) (why : Reason)
  /-- exactly `n` present labels equal register `v`, or refuse for `why` -/
  | countEq (v n : Nat) (why : Reason)
  /-- no present label, written into register `src`, passes `body`; or refuse for `why` -/
  | scanNone (src : Nat) (body : List MInstr) (why : Reason)
  | fail (why : Reason)
  /-- commit: the occurrence of use `u` leaves -/
  | remove (u : Nat)
  /-- commit: `k` names are minted -/
  | mint (k : Nat)
  /-- commit: an occurrence labelled by register `v` is made with the next identity -/
  | add (v : Nat)

/-- What a decision is given: the parameters and the identities of the uses (takes, then reads). -/
structure Ctx where
  params : List Tm
  occs : List Nat

def Ctx.param (c : Ctx) (k : Nat) : Tm := c.params.getD k default
def Ctx.occ (c : Ctx) (u : Nat) : Nat := c.occs.getD u 0

/-- The machine: registers, the state, and the identities made so far. -/
structure Mach where
  rs : Regs
  st : St
  made : List Nat

def Instr.exec (c : Ctx) (m : Mach) : Instr → Except Reason Mach
  | .loadParam dst k => .ok { m with rs := m.rs.write dst (c.param k) }
  | .loadConst dst t => .ok { m with rs := m.rs.write dst t }
  | .loadFresh dst j => .ok { m with rs := m.rs.write dst (.name (m.st.names + j)) }
  | .mkApp dst f args => .ok { m with rs := m.rs.write dst (.app f (args.map m.rs)) }
  | .needName k => if k < m.st.names then .ok m else .error .shapes
  | .paramMinted k => if (c.param k).minted m.st.names = true then .ok m else .error .shapes
  | .occNonzero u => if c.occ u ≠ 0 then .ok m else .error .shapes
  | .occDistinct u v why => if c.occ u ≠ c.occ v then .ok m else .error why
  | .lookup u dst => match labelOf m.st (c.occ u) with
      | some l => .ok { m with rs := m.rs.write dst l }
      | none => .error .fits
  | .test i why => match i.exec m.st.names m.rs with
      | some rs => .ok { m with rs := rs }
      | none => .error why
  | .countEq v n why =>
      if (m.st.present.filter fun row => decide (row.label = m.rs v)).length = n then .ok m
      else .error why
  | .scanNone src body why =>
      if m.st.present.any (fun row => (MInstr.run m.st.names body (m.rs.write src row.label)).isSome)
      then .error why else .ok m
  | .fail why => .error why
  | .remove u => .ok { m with st := { m.st with present := m.st.present.filter fun row => row.id != c.occ u } }
  | .mint k => .ok { m with st := { m.st with names := m.st.names + k } }
  | .add v => .ok { m with
      st := { m.st with present := m.st.present ++ [⟨m.st.nextId, m.rs v⟩], nextId := m.st.nextId + 1 }
      made := m.made ++ [m.st.nextId] }

/-- Run instructions in order. On a refusal, the reason and the machine as the instructions before
it left it. -/
def run (c : Ctx) : List Instr → Mach → Option Reason × Mach
  | [], m => (none, m)
  | i :: is, m => match i.exec c m with
      | .ok m' => run c is m'
      | .error r => (some r, m)

/-- An instruction that leaves the state and the made identities alone. -/
def Instr.pure : Instr → Bool
  | .remove _ => false
  | .mint _ => false
  | .add _ => false
  | _ => true

/-- A program: its checks, then its commit. -/
structure Prog where
  checks : List Instr
  commit : List Instr

inductive Verdict where
  | admitted
  | refused (r : Reason)
  deriving DecidableEq

def Prog.start (s : St) : Mach := ⟨fun _ => default, s, []⟩

/-- Admission alone: the verdict, the state afterwards, and the first name a firing would mint. -/
def Prog.admits (P : Prog) (c : Ctx) (s : St) : Verdict × St × Nat :=
  match run c P.checks (Prog.start s) with
  | (none, m) => (.admitted, m.st, m.st.names)
  | (some r, m) => (.refused r, m.st, m.st.names)

/-- The firing: the verdict, the state afterwards, and the identities made. -/
def Prog.fire (P : Prog) (c : Ctx) (s : St) : Verdict × St × List Nat :=
  match run c P.checks (Prog.start s) with
  | (none, m) => match run c P.commit m with
      | (none, m') => (.admitted, m'.st, m'.made)
      | (some r, m') => (.refused r, m'.st, m'.made)
  | (some r, m) => (.refused r, m.st, m.made)

/-! ### Laws of runs -/

theorem run_append (c : Ctx) (A B : List Instr) (m : Mach) :
    run c (A ++ B) m = match run c A m with
      | (none, m') => run c B m'
      | (some r, m') => (some r, m') := by
  induction A generalizing m with
  | nil => rfl
  | cons i is ih =>
      simp only [List.cons_append, run]
      cases i.exec c m with
      | ok m' => exact ih m'
      | error r => rfl

theorem exec_pure {c : Ctx} {m m' : Mach} {i : Instr} (hp : i.pure = true)
    (h : i.exec c m = .ok m') : m'.st = m.st ∧ m'.made = m.made := by
  cases i with
  | remove u => simp [Instr.pure] at hp
  | mint k => simp [Instr.pure] at hp
  | add v => simp [Instr.pure] at hp
  | loadParam dst k => simp only [Instr.exec, Except.ok.injEq] at h; subst h; exact ⟨rfl, rfl⟩
  | loadConst dst t => simp only [Instr.exec, Except.ok.injEq] at h; subst h; exact ⟨rfl, rfl⟩
  | loadFresh dst j => simp only [Instr.exec, Except.ok.injEq] at h; subst h; exact ⟨rfl, rfl⟩
  | mkApp dst f args => simp only [Instr.exec, Except.ok.injEq] at h; subst h; exact ⟨rfl, rfl⟩
  | needName k =>
      simp only [Instr.exec] at h
      split at h
      · simp only [Except.ok.injEq] at h; subst h; exact ⟨rfl, rfl⟩
      · cases h
  | paramMinted k =>
      simp only [Instr.exec] at h
      split at h
      · simp only [Except.ok.injEq] at h; subst h; exact ⟨rfl, rfl⟩
      · cases h
  | occNonzero u =>
      simp only [Instr.exec] at h
      split at h
      · simp only [Except.ok.injEq] at h; subst h; exact ⟨rfl, rfl⟩
      · cases h
  | occDistinct u v why =>
      simp only [Instr.exec] at h
      split at h
      · simp only [Except.ok.injEq] at h; subst h; exact ⟨rfl, rfl⟩
      · cases h
  | lookup u dst =>
      simp only [Instr.exec] at h
      split at h
      · simp only [Except.ok.injEq] at h; subst h; exact ⟨rfl, rfl⟩
      · cases h
  | test i why =>
      simp only [Instr.exec] at h
      split at h
      · simp only [Except.ok.injEq] at h; subst h; exact ⟨rfl, rfl⟩
      · cases h
  | countEq v n why =>
      simp only [Instr.exec] at h
      split at h
      · simp only [Except.ok.injEq] at h; subst h; exact ⟨rfl, rfl⟩
      · cases h
  | scanNone src body why =>
      simp only [Instr.exec] at h
      split at h
      · cases h
      · simp only [Except.ok.injEq] at h; subst h; exact ⟨rfl, rfl⟩
  | fail why => cases h

/-- **Pure instructions change nothing but registers**, whether the run ends in a refusal or not. -/
theorem run_pure (c : Ctx) : ∀ (is : List Instr) (m : Mach), (∀ i ∈ is, i.pure = true) →
    (run c is m).2.st = m.st ∧ (run c is m).2.made = m.made
  | [], _, _ => ⟨rfl, rfl⟩
  | i :: is, m, h => by
      simp only [run]
      cases hi : i.exec c m with
      | ok m' =>
          have e := exec_pure (h i (List.mem_cons_self ..)) hi
          have r := run_pure c is m' (fun j hj => h j (List.mem_cons_of_mem _ hj))
          exact ⟨r.1.trans e.1, r.2.trans e.2⟩
      | error r => exact ⟨rfl, rfl⟩

#print axioms run_append
#print axioms run_pure

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SpecializedAdmission
