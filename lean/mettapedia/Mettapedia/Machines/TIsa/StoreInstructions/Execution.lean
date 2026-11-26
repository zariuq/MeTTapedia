import Mettapedia.Machines.TIsa.P1WordExecution
import Mettapedia.Machines.TIsa.Derivation.Solutions

/-!
# t-ISA with store instructions

t-ISA p1 has scalar words, control, loops and memory; the rule engine's operations are not among
its instructions. This module extends p1's semantics (`P1WordExecution`) with the instructions the
derived abstract machine of the transform calculus needs and p1 lacks (`Derivation.Instructions`):

* `size d`: the number of occurrences of the store, into a word register;
* `open level`: the match at `level` starts empty (a rule is entered);
* `premise role pattern level index d`: try the occurrence at the store index held in `index` for a
  premise, against the match at `level`; when the occurrence is allowed and its value matches, the
  extended match is the match at `level + 1`, and `d` is `1`, otherwise `0`;
* `test goal level d`: a determinate goal (tell, check, collect, produce) on the match at `level`,
  updating it in place; `d` is `1` when it is solved, otherwise `0`;
* `take level slot`, `make level slot`: publish the `slot`-th taken occurrence or made value of the
  match at `level`.

The store is the derived machine's store and matches are the derived machine's matches: the
extension is semantic, over the term syntax of a `Matcher`, and fixes no memory layout. Control,
loops, FUND and RETURN are p1's own, unchanged: the p1 source admits a store-effect profile, and executing a
promoted word program is executing it in the word profile (`execute_ofP1`), with the store and the matches untouched. Choice points are p1 loops: the
derived machine's backtracking over the occurrences of a premise is an `EARLY_EXIT_LOOP` over store
indices (`StoreInstructions.FiringLoop`).
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.StoreInstructions

open P1Source
open Derivation

universe u v w e

/-- The p1 Transform profile uses rule patterns and guards as operands.
The word-only profile does not require a term representation. -/
abbrev TransformOp (T : Type u) := P1Source.StoreOp Role T (Determinate T)
abbrev Source (T : Type u) := P1Source.Statement (TransformOp T) true

variable {T : Type u} {V : Type v} {B : Type w}

/-- **The state**: p1's machine state, the store, and the match at each level. -/
structure State (V : Type v) (B : Type w) where
  machine : P1WordExecution.State
  store : Derivation.Store V
  levels : ℕ → Match V B

namespace State

/-- Write a word register. -/
def write (st : State V B) (dst : Reg) (value : Word) : State V B :=
  {st with machine := st.machine.write dst value}

/-- Set the match at a level. -/
def setLevel (st : State V B) (level : ℕ) (m : Match V B) : State V B :=
  {st with levels := Function.update st.levels level m}

end State

/-- A phase which has neither changed the budget nor paid a debit. -/
structure SameFuel (before after : State V B) : Prop where
  budget : after.machine.budget = before.machine.budget
  spent : after.machine.spent = before.machine.spent

theorem SameFuel.trans {first middle last : State V B} (one : SameFuel first middle) (two : SameFuel middle last) :
    SameFuel first last :=
  ⟨two.budget.trans one.budget, two.spent.trans one.spent⟩

/-- How a statement ends: it continues, or the program returns. -/
inductive Flow (V : Type v) (B : Type w) where
  | continuing (state : State V B)
  | returned (status : ExitStatus) (payload : Word) (state : State V B)

namespace Flow

def after : Flow V B → State V B
  | .continuing st | .returned _ _ st => st

def thenContinue (first : Flow V B) (next : State V B → Flow V B) : Flow V B :=
  match first with
  | .continuing st => next st
  | .returned status payload st => .returned status payload st

/-- A p1 flow, with the store and the matches of a state. -/
def lift (st : State V B) : P1WordExecution.Flow → Flow V B
  | .continuing machine => .continuing {st with machine}
  | .returned status payload machine => .returned status payload {st with machine}

end Flow

/-- Only opening, extending, and testing a match are profile-specific.
Occurrence ordinals, result words, and take/make are shared. -/
structure StoreProfile (T : Type u) (G : Type u) (V : Type v) (B : Type w) where
  initial : Match V B
  attempt : Role → T → Match V B → (ℕ × V) → Option (Match V B)
  test : Derivation.Store V → G → Match V B → Option (Match V B)

def StoreProfile.step {G : Type u} (profile : StoreProfile T G V B) (st : State V B) :
    P1Source.StoreOp Role T G → Except ExitStatus (State V B)
  | .size dst => .ok (st.write dst (BitVec.ofNat 64 st.store.occurrences.length))
  | .open level => .ok (st.setLevel level profile.initial)
  | .premise role pattern level index dst =>
      match st.store.occurrences[(st.machine.registers index).toNat]? with
      | none => .error .invalidInput
      | some x =>
          match profile.attempt role pattern (st.levels level) x with
          | some m' => .ok ((st.setLevel (level + 1) m').write dst 1)
          | none => .ok (st.write dst 0)
  | .test goal level dst =>
      match profile.test st.store goal (st.levels level) with
      | some m' => .ok ((st.setLevel level m').write dst 1)
      | none => .ok (st.write dst 0)
  | .take level slot =>
      match (st.levels level).taken[slot]? with
      | some o => .ok {st with store := st.store.remove o}
      | none => .error .invalidInput
  | .make level slot =>
      match (st.levels level).made[slot]? with
      | some w => .ok {st with store := st.store.add w}
      | none => .error .invalidInput

def StoreProfile.ground [DecidableEq V] (M : Matcher T V B) : StoreProfile T (Determinate T) V B :=
  ⟨Match.start M, Derivation.attempt M, fun store goal entry => goal.apply M store entry⟩

abbrev TransformOp.execute [DecidableEq V] (M : Matcher T V B) := (StoreProfile.ground M).step

abbrev EffectStep (effect : Type e) (V : Type v) (B : Type w) :=
  State V B → effect → Except ExitStatus (State V B)

/-- Read the instruction in its p1 profile. The word variant uses exactly
the existing word executor; the other variant uses the chosen store effect. -/
def executeInstructionWith {E : Type e} (step : EffectStep E V B)
    (st : State V B) (code : P1Source.Instruction E true) :
    Except ExitStatus (State V B) :=
  match code.view with
  | .inl i =>
    match P1WordExecution.instruction st.machine i with
    | .ok machine => .ok {st with machine}
    | .error status => .error status
  | .inr op => step st op

abbrev executeInstruction [DecidableEq V] (M : Matcher T V B) :=
  executeInstructionWith (TransformOp.execute M)

def fail (status : ExitStatus) (st : State V B) : Flow V B := .returned status status.word st

/-- p1's FUND. -/
def fund (st : State V B) (units : BitVec 32) : Flow V B :=
  let debit := units.zeroExtend 64
  if st.machine.budget - st.machine.spent < debit then fail .exhausted st
  else .continuing {st with machine := {st.machine with spent := st.machine.spent + debit}}

/-- p1's loop guard. -/
def continueLoop (st : State V B) (guard : Option Reg) (next : State V B → Flow V B) : Flow V B :=
  match guard with
  | none => next st
  | some condition =>
    if st.machine.registers condition = 1 then next st
    else if st.machine.registers condition = 0 then .continuing st
    else fail .invalidInput st

/-- p1's loops. -/
def loop (body : State V B → Flow V B) (index : Reg) (guard : Option Reg) :
    ℕ → State V B → Flow V B
  | 0, st => .continuing st
  | remaining + 1, st =>
    continueLoop st guard fun start =>
      (body start).thenContinue fun following =>
        continueLoop following guard fun next =>
          loop body index guard remaining (next.write index (next.machine.registers index + 1))

/-- p1's control is independent of how a store instruction interprets
its operands. In particular, branching, fuel, and failures are the same
throughout the ground and symbolic profiles. -/
def executeWith {E : Type e} (step : EffectStep E V B)
    (st : State V B) : P1Source.Statement E true → Flow V B
  | .skip => .continuing st
  | .instruction code =>
    match executeInstructionWith step st code with
    | .ok following => .continuing following
    | .error status => fail status st
  | .seq first second => (executeWith step st first).thenContinue fun next => executeWith step next second
  | .branch condition yes no =>
    if st.machine.registers condition = 1 then executeWith step st yes
    else if st.machine.registers condition = 0 then executeWith step st no
    else fail .invalidInput st
  | .counted index bound cap body =>
    if cap.toNat < (st.machine.registers bound).toNat then fail .unsupported st
    else loop (fun next => executeWith step next body) index none
      (st.machine.registers bound).toNat (st.write index 0)
  | .early index bound continuation cap body =>
    if cap.toNat < (st.machine.registers bound).toNat then fail .unsupported st
    else loop (fun next => executeWith step next body) index (some continuation)
      (st.machine.registers bound).toNat (st.write index 0)
  | .fund units => fund st units
  | .ret outcome result => .returned outcome (st.machine.registers result) st

abbrev execute [DecidableEq V] (M : Matcher T V B) := executeWith (TransformOp.execute M)

theorem executeWith_seq {E : Type e} (step : EffectStep E V B) (st : State V B)
    (first rest : P1Source.Statement E true) :
    executeWith step st (.seq first rest) =
      (executeWith step st first).thenContinue (fun next => executeWith step next rest) :=
  rfl

/-! ## p1 is a sub-language with the same semantics -/

theorem lift_thenContinue (st : State V B) (first : P1WordExecution.Flow)
    (next : P1WordExecution.State → P1WordExecution.Flow) (next' : State V B → Flow V B)
    (agree : ∀ machine, next' {st with machine} = Flow.lift st (next machine)) :
    (Flow.lift st first).thenContinue next' = Flow.lift st (first.thenContinue next) := by
  cases first with
  | continuing machine => exact agree machine
  | returned status payload machine => rfl

theorem lift_continueLoop (st : State V B) (machine : P1WordExecution.State) (guard : Option Reg)
    (next : P1WordExecution.State → P1WordExecution.Flow) (next' : State V B → Flow V B)
    (agree : ∀ machine, next' {st with machine} = Flow.lift st (next machine)) :
    continueLoop {st with machine} guard next' =
      Flow.lift st (P1WordExecution.continueLoop machine guard next) := by
  cases guard with
  | none => exact agree machine
  | some condition =>
      simp only [continueLoop, P1WordExecution.continueLoop]
      split_ifs <;> first | exact agree machine | rfl

theorem lift_loop (st : State V B) (body : P1WordExecution.State → P1WordExecution.Flow)
    (body' : State V B → Flow V B)
    (agree : ∀ machine, body' {st with machine} = Flow.lift st (body machine))
    (index : Reg) (guard : Option Reg) :
    ∀ (remaining : ℕ) (machine : P1WordExecution.State),
      loop body' index guard remaining {st with machine} =
        Flow.lift st (P1WordExecution.loop body index guard remaining machine)
  | 0, machine => rfl
  | remaining + 1, machine => by
      simp only [loop, P1WordExecution.loop]
      apply lift_continueLoop
      intro started
      rw [agree]
      apply lift_thenContinue
      intro following
      apply lift_continueLoop
      intro latched
      exact lift_loop st body body' agree index guard remaining _

/-- A word program has identical behavior in every store-effect
profile and never calls the store effect. -/
theorem executeWith_ofP1 {E : Type e} (step : EffectStep E V B) (st : State V B) :
    ∀ (s : P1Source.Stmt) (machine : P1WordExecution.State),
      executeWith step {st with machine} (s.toStore) =
        Flow.lift st (P1WordExecution.execute machine s)
  | .skip, _ => rfl
  | .instruction i, machine => by
      simp only [P1Source.Statement.toStore, executeWith, executeInstructionWith, P1Source.Instruction.view_toStore,
        P1WordExecution.execute]
      cases P1WordExecution.instruction machine i <;> rfl
  | .seq first second, machine => by
      simp only [P1Source.Statement.toStore, executeWith, P1WordExecution.execute]
      rw [executeWith_ofP1 step st first machine]
      apply lift_thenContinue
      intro following
      exact executeWith_ofP1 step st second following
  | .branch c yes no, machine => by
      simp only [P1Source.Statement.toStore, executeWith, P1WordExecution.execute]
      split_ifs
      · exact executeWith_ofP1 step st yes machine
      · exact executeWith_ofP1 step st no machine
      · rfl
  | .counted index bound cap body, machine => by
      simp only [P1Source.Statement.toStore, executeWith, P1WordExecution.execute]
      split_ifs
      · rfl
      · exact lift_loop st _ _ (fun m => executeWith_ofP1 step st body m) index none _ _
  | .early index bound k cap body, machine => by
      simp only [P1Source.Statement.toStore, executeWith, P1WordExecution.execute]
      split_ifs
      · rfl
      · exact lift_loop st _ _ (fun m => executeWith_ofP1 step st body m) index (some k) _ _
  | .ret outcome source, _ => rfl
  | .fund units, machine => by
      simp only [P1Source.Statement.toStore, executeWith, P1WordExecution.execute, fund, P1WordExecution.fund]
      split_ifs <;> rfl

theorem execute_ofP1 [DecidableEq V] (M : Matcher T V B) (st : State V B) :
    ∀ (s : P1Source.Stmt) (machine : P1WordExecution.State),
      execute M {st with machine} (s.toStore) =
        Flow.lift st (P1WordExecution.execute machine s) :=
  executeWith_ofP1 (TransformOp.execute M) st

section StoreUpdates

variable {G : Type u}

/-- Take the occurrences of slots `i, i+1, …` of the match at a level. -/
def takesFrom (level : ℕ) : ℕ → ℕ → P1Source.Statement (P1Source.StoreOp Role T G) true
  | _, 0 => .skip
  | i, n + 1 => .seq (.instruction (.transform (.take level i))) (takesFrom level (i + 1) n)

/-- Make the values of slots `i, i+1, …` of the match at a level. -/
def makesFrom (level : ℕ) : ℕ → ℕ → P1Source.Statement (P1Source.StoreOp Role T G) true
  | _, 0 => .skip
  | i, n + 1 => .seq (.instruction (.transform (.make level i))) (makesFrom level (i + 1) n)

theorem takesFrom_execute (profile : StoreProfile T G V B) (level : ℕ) (m : Match V B) :
    ∀ (n i : ℕ) (st : State V B), st.levels level = m → (m.taken.drop i).length = n →
      executeWith profile.step st (takesFrom level i n) =
        .continuing {st with store := st.store.takeAll (m.taken.drop i)}
  | 0, i, st, _, lengths => by
      have empty : m.taken.drop i = [] := List.eq_nil_of_length_eq_zero lengths
      simp [takesFrom, executeWith, empty, Store.takeAll]
  | n + 1, i, st, current, lengths => by
      cases dropped : m.taken.drop i with
      | nil => rw [dropped] at lengths; simp at lengths
      | cons o os =>
          have slot : m.taken[i]? = some o := by
            rw [← List.head?_drop, dropped]
            rfl
          have rest : m.taken.drop (i + 1) = os := by
            rw [← List.drop_drop, dropped]
            rfl
          rw [dropped] at lengths
          simp only [takesFrom, executeWith_seq]
          have first : executeWith profile.step st (.instruction (.transform (.take level i))) =
              .continuing {st with store := st.store.remove o} := by
            simp [executeWith, executeInstructionWith, P1Source.Instruction.view, StoreProfile.step, current, slot]
          rw [first]
          simp only [Flow.thenContinue]
          rw [takesFrom_execute profile level m n (i + 1) {st with store := st.store.remove o} current
            (by rw [rest]; simpa using lengths), rest]
          rfl

theorem makesFrom_execute (profile : StoreProfile T G V B) (level : ℕ) (m : Match V B) :
    ∀ (n i : ℕ) (st : State V B), st.levels level = m → (m.made.drop i).length = n →
      executeWith profile.step st (makesFrom level i n) =
        .continuing {st with store := st.store.makeAll (m.made.drop i)}
  | 0, i, st, _, lengths => by
      have empty : m.made.drop i = [] := List.eq_nil_of_length_eq_zero lengths
      simp [makesFrom, executeWith, empty, Store.makeAll]
  | n + 1, i, st, current, lengths => by
      cases dropped : m.made.drop i with
      | nil => rw [dropped] at lengths; simp at lengths
      | cons w ws =>
          have slot : m.made[i]? = some w := by
            rw [← List.head?_drop, dropped]
            rfl
          have rest : m.made.drop (i + 1) = ws := by
            rw [← List.drop_drop, dropped]
            rfl
          rw [dropped] at lengths
          simp only [makesFrom, executeWith_seq]
          have first : executeWith profile.step st (.instruction (.transform (.make level i))) =
              .continuing {st with store := st.store.add w} := by
            simp [executeWith, executeInstructionWith, P1Source.Instruction.view, StoreProfile.step, current, slot]
          rw [first]
          simp only [Flow.thenContinue]
          rw [makesFrom_execute profile level m n (i + 1) {st with store := st.store.add w} current
            (by rw [rest]; simpa using lengths), rest]
          rfl

end StoreUpdates

end Mettapedia.Machines.TIsa.StoreInstructions
