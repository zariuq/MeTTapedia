import Mettapedia.Machines.TIsa.StoreInstructions.Execution
import Mettapedia.Machines.TIsa.Derivation.Machine
import Mettapedia.Machines.TIsa.Derivation.Semantics

/-!
# The firing loop of the transform calculus, compiled to t-ISA

A program of rules compiles to one t-ISA program with store instructions (`program`) that performs
one firing of the derived machine: it searches the rules in order, matches each rule's premises
against the store, asks its determinate goals, and publishes the first firing it finds.

The derived machine's control becomes p1 control:

* the choice point of a premise is an `EARLY_EXIT_LOOP` over the store's indices, whose body
  matches the occurrence at the loop index (`premise`) and, when it matches, runs the rest of the
  rule's code; the loop's latch is the derived machine's `retry`;
* a determinate goal is a `test` followed by an `IF` on its result;
* the commit is `FUND 1`, then `take` and `make` for the match, then clearing the loop
  continuation register, which ends every enclosing loop;
* the rules are a sequence of blocks, each opened by `open 0` and followed by an `IF` on the
  continuation register: a firing returns `FIRED` (`completed`), the end of the rules returns
  `REFUSED`.

The registers: the store size in `v1`, the loop continuation in `v2`, the loop index of the premise
at level `ℓ` in `v(3+ℓ)`, results of matches and goals in `v11`; at most eight premises per rule.
Every store size up to the loop cap is supported.

## The simulation

* `program_fires`: the compiled program returns `REFUSED` with the store unchanged when the
  evaluator finds no firing; when it finds one, it returns `FIRED` with the first firing published
  and one unit paid, or `EXHAUSTED` with the store unchanged when no unit is left.
* `Derivation.search_commits`: the derived machine, from a store, reaches the same three ends: it
  halts quiescent, halts exhausted, or reaches the next search on the published store with one
  unit less.
* `program_simulates_machine`: the two together. One invocation of the compiled program realizes
  exactly one search-and-firing of the derived machine, from the same store and allowance, and
  pays exactly what the machine pays.
* `invoke_run`, `invoke_simulates_quiescent`, `invoke_simulates_exhausted`: invoked once per firing, as t-ISA leaf invocations are,
  the compiled program realizes the whole run: it ends with the machine's outcome and store, when
  every store of the run fits the loop cap.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.StoreInstructions

open P1Source
open Derivation

universe u v w

/-! ## Register layout and compilation -/

/-- The register holding the store size. -/
def boundReg : Reg := 1

/-- The loop continuation register: `1` while searching, `0` once a firing is published. -/
def flagReg : Reg := 2

/-- The register receiving the result of a match or a goal. -/
def testReg : Reg := 11

/-- The loop index register of the premise at a level. -/
def indexReg (level : ℕ) : Reg := ⟨min (3 + level) 10, by omega⟩

variable {T : Type u} {V : Type v} {B : Type w}

/-- Run statements one after another. -/
def seqAll : List (Source T) → Source T
  | [] => .skip
  | s :: rest => .seq s (seqAll rest)

/-- **The commit**: pay one unit, publish the match at the level, and clear the continuation. -/
def publication (level takes makes : ℕ) : Source T :=
  .seq (.fund 1) (.seq (takesFrom level 0 takes)
    (.seq (makesFrom level 0 makes) (.instruction (.immediate .boolean flagReg 0))))

/-- **The code of a rule's goals** from a level: a premise is a loop over the store, a determinate
goal a test. -/
def body (cap : BitVec 32) (takes makes : ℕ) : ℕ → List (Goal T) → Source T
  | level, [] => publication level takes makes
  | level, .premise role pattern :: gs =>
      .early (indexReg level) boundReg flagReg cap
        (.seq (.instruction (.transform (.premise role pattern level (indexReg level) testReg)))
          (.branch testReg (body cap takes makes (level + 1) gs) .skip))
  | level, .determinate d :: gs =>
      .seq (.instruction (.transform (.test d level testReg)))
        (.branch testReg (body cap takes makes level gs) .skip)

/-- A rule's block: open the empty match, then its goals. -/
def ruleBlock (cap : BitVec 32) (r : Rule T) : Source T :=
  .seq (.instruction (.transform (.open 0))) (body cap r.body.take.length r.body.produce.length 0 (goals r))

/-- The rules in order: after each block, a published firing returns `FIRED`. -/
def rulesCode (cap : BitVec 32) : List (Rule T) → Source T
  | [] => .ret .refused testReg
  | r :: rs => .seq (ruleBlock cap r) (.branch flagReg (rulesCode cap rs) (.ret .completed testReg))

/-- **The compiled firing loop of a program.** -/
def program (cap : BitVec 32) (P : List (Rule T)) : Source T :=
  .seq (.instruction (.immediate .boolean flagReg 1))
    (.seq (.instruction (.transform (.size boundReg))) (rulesCode cap P))

/-- The number of premises of a goal list. -/
def premiseCount : List (Goal T) → ℕ
  | [] => 0
  | .premise _ _ :: gs => premiseCount gs + 1
  | .determinate _ :: gs => premiseCount gs

/-! ## Invariants -/

/-- Everything but the scratch registers and matches above a level agrees. -/
structure Kept (level : ℕ) (before after : State V B) : Prop where
  store : after.store = before.store
  regions : after.machine.regions = before.machine.regions
  frame : after.machine.frame = before.machine.frame
  memory : after.machine.memory = before.machine.memory
  budget : after.machine.budget = before.machine.budget
  spent : after.machine.spent = before.machine.spent
  registers : ∀ r : Reg, r.val < 3 + level → after.machine.registers r = before.machine.registers r
  levels : ∀ l, l < level → after.levels l = before.levels l

namespace Kept

theorem refl (level : ℕ) (st : State V B) : Kept level st st :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl, fun _ _ => rfl⟩

theorem trans {level : ℕ} {a b c : State V B} (first : Kept level a b) (second : Kept level b c) :
    Kept level a c :=
  ⟨second.store.trans first.store, second.regions.trans first.regions, second.frame.trans first.frame,
    second.memory.trans first.memory, second.budget.trans first.budget, second.spent.trans first.spent,
    fun r below => (second.registers r below).trans (first.registers r below),
    fun l below => (second.levels l below).trans (first.levels l below)⟩

theorem mono {level level' : ℕ} {a b : State V B} (kept : Kept level' a b) (le : level ≤ level') :
    Kept level a b :=
  ⟨kept.store, kept.regions, kept.frame, kept.memory, kept.budget, kept.spent,
    fun r below => kept.registers r (by omega), fun l below => kept.levels l (by omega)⟩

theorem write {level : ℕ} (st : State V B) (r : Reg) (value : Word) (high : 3 + level ≤ r.val) :
    Kept level st (st.write r value) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, fun _ _ => rfl⟩
  intro r' below
  have different : r' ≠ r := fun same => by subst same; omega
  exact Function.update_of_ne different _ _

theorem setLevel {level : ℕ} (st : State V B) (l : ℕ) (m : Match V B) (high : level ≤ l) :
    Kept level st (st.setLevel l m) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl, ?_⟩
  intro l' below
  have different : l' ≠ l := by omega
  exact Function.update_of_ne different _ _

end Kept

/-- A state ready to search the store `s` at a level, with the match `m` there. -/
structure Ready (s : Store V) (level : ℕ) (m : Match V B) (st : State V B) : Prop where
  store : st.store = s
  current : st.levels level = m
  bound : st.machine.registers boundReg = BitVec.ofNat 64 s.occurrences.length
  flag : st.machine.registers flagReg = 1
  funds : st.machine.spent.toNat ≤ st.machine.budget.toNat

/-- A committed firing: the match published, the continuation cleared, one unit paid. -/
structure Published (s : Store V) (m : Match V B) (before after : State V B) : Prop where
  store : after.store = publish s m
  flag : after.machine.registers flagReg = 0
  spent : after.machine.spent = before.machine.spent + 1
  budget : after.machine.budget = before.machine.budget
  regions : after.machine.regions = before.machine.regions
  frame : after.machine.frame = before.machine.frame
  memory : after.machine.memory = before.machine.memory

/-- A firing found without a unit to pay for it: nothing published, nothing paid. -/
structure Unpaid (s : Store V) (before after : State V B) : Prop where
  store : after.store = s
  spent : after.machine.spent = before.machine.spent
  budget : after.machine.budget = before.machine.budget
  regions : after.machine.regions = before.machine.regions
  frame : after.machine.frame = before.machine.frame
  memory : after.machine.memory = before.machine.memory

/-- **What a search does**, given the matches the evaluator lists from its position: with none, it
continues with everything kept; with some, it publishes the first and pays, or ends exhausted when
no unit is left. -/
def Searched (s : Store V) (level : ℕ) (before : State V B) : List (Match V B) → Flow V B → Prop
  | [], flow => ∃ after, flow = .continuing after ∧ Kept level before after
  | m :: _, flow =>
      (before.machine.spent.toNat < before.machine.budget.toNat ∧
        ∃ after, flow = .continuing after ∧ Published s m before after) ∨
      (before.machine.budget.toNat ≤ before.machine.spent.toNat ∧
        ∃ payload after, flow = .returned .exhausted payload after ∧ Unpaid s before after)

/-- A search's description transfers along kept states. -/
theorem Searched.of_kept {s : Store V} {level : ℕ} {st st' : State V B}
    (kept : Kept level st st') :
    ∀ {L : List (Match V B)} {flow : Flow V B}, Searched s level st' L flow → Searched s level st L flow
  | [], _, ⟨after, flowing, keeps⟩ => ⟨after, flowing, kept.trans keeps⟩
  | _ :: _, _, .inl ⟨paid, after, flowing, published⟩ => by
      refine .inl ⟨?_, after, flowing, ?_⟩
      · rw [← kept.spent, ← kept.budget]; exact paid
      · exact ⟨published.store, published.flag, published.spent.trans (by rw [kept.spent]),
          published.budget.trans kept.budget, published.regions.trans kept.regions,
          published.frame.trans kept.frame, published.memory.trans kept.memory⟩
  | _ :: _, _, .inr ⟨unpaid, payload, after, flowing, nothing⟩ => by
      refine .inr ⟨?_, payload, after, flowing, ?_⟩
      · rw [← kept.spent, ← kept.budget]; exact unpaid
      · exact ⟨nothing.store, nothing.spent.trans kept.spent, nothing.budget.trans kept.budget,
          nothing.regions.trans kept.regions, nothing.frame.trans kept.frame,
          nothing.memory.trans kept.memory⟩

/-! ## Publication -/

section Publication

variable [DecidableEq V] (M : Matcher T V B)

theorem execute_seq (st : State V B) (first second : Source T) :
    execute M st (.seq first second) = (execute M st first).thenContinue fun next => execute M next second :=
  rfl

theorem one_extend : BitVec.zeroExtend 64 (1 : BitVec 32) = (1 : BitVec 64) := by decide

omit [DecidableEq V] in
theorem fund_one_iff (st : State V B) (funds : st.machine.spent.toNat ≤ st.machine.budget.toNat) :
    st.machine.budget - st.machine.spent < (1 : BitVec 64) ↔
      st.machine.budget.toNat ≤ st.machine.spent.toNat := by
  rw [BitVec.lt_def, BitVec.toNat_sub_of_le funds]
  have : (1 : BitVec 64).toNat = 1 := by decide
  rw [this]
  omega

omit [DecidableEq V] in
theorem fund_exhausted (st : State V B) (funds : st.machine.spent.toNat ≤ st.machine.budget.toNat)
    (broke : st.machine.budget.toNat ≤ st.machine.spent.toNat) : fund st 1 = fail .exhausted st := by
  simp only [fund, one_extend]
  rw [if_pos ((fund_one_iff st funds).mpr broke)]

omit [DecidableEq V] in
theorem fund_paid (st : State V B) (funds : st.machine.spent.toNat ≤ st.machine.budget.toNat)
    (paying : st.machine.spent.toNat < st.machine.budget.toNat) :
    fund st 1 = .continuing {st with machine := {st.machine with spent := st.machine.spent + 1}} := by
  simp only [fund, one_extend]
  rw [if_neg (fun exhausted => by have := (fund_one_iff st funds).mp exhausted; omega)]

theorem execute_immediate (st : State V B) (dst : Reg) (value : Word) :
    execute M st (.instruction (.immediate .boolean dst value)) = .continuing (st.write dst value) := by
  rfl

/-- **The commit publishes the match and pays one unit**, or ends exhausted with nothing done. -/
theorem publication_searched (s : Store V) (level : ℕ) (m : Match V B) (st : State V B)
    (ready : Ready s level m st) :
    Searched s level st [m]
      (execute M st (publication level m.taken.length m.made.length)) := by
  rw [publication, execute_seq]
  change Searched s level st [m] ((fund st 1).thenContinue fun next => execute M next _)
  by_cases broke : st.machine.budget.toNat ≤ st.machine.spent.toNat
  · rw [fund_exhausted st ready.funds broke]
    exact .inr ⟨broke, _, st, rfl, ready.store, rfl, rfl, rfl, rfl, rfl⟩
  · rw [fund_paid st ready.funds (by omega)]
    simp only [Flow.thenContinue]
    let paid : State V B := {st with machine := {st.machine with spent := st.machine.spent + 1}}
    have takes : execute M paid (takesFrom level 0 m.taken.length) =
        .continuing {paid with store := paid.store.takeAll (m.taken.drop 0)} :=
      takesFrom_execute (StoreProfile.ground M) level m m.taken.length 0 paid ready.current (by simp)
    let taken : State V B := {paid with store := paid.store.takeAll (m.taken.drop 0)}
    have makes : execute M taken (makesFrom level 0 m.made.length) =
        .continuing {taken with store := taken.store.makeAll (m.made.drop 0)} :=
      makesFrom_execute (StoreProfile.ground M) level m m.made.length 0 taken ready.current (by simp)
    change Searched s level st [m] ((execute M paid (takesFrom level 0 m.taken.length)).thenContinue
      fun next => execute M next (.seq (makesFrom level 0 m.made.length) _))
    rw [takes]
    simp only [Flow.thenContinue]
    change Searched s level st [m] ((execute M taken (makesFrom level 0 m.made.length)).thenContinue
      fun next => execute M next _)
    rw [makes]
    simp only [Flow.thenContinue]
    rw [execute_immediate]
    refine .inl ⟨by omega, _, rfl, ?_⟩
    refine ⟨?_, ?_, rfl, rfl, rfl, rfl, rfl⟩
    · simp only [List.drop_zero, State.write, taken, paid, ready.store]
      rfl
    · simp [State.write, P1WordExecution.State.write]

end Publication

/-! ## The search -/

section Search

variable [DecidableEq V] (M : Matcher T V B)

theorem indexReg_val {level : ℕ} (small : level ≤ 7) : (indexReg level).val = 3 + level := by
  simp only [indexReg]
  omega

omit [DecidableEq V] in
theorem write_same (st : State V B) (r : Reg) (value : Word) :
    (st.write r value).machine.registers r = value := by
  simp [State.write, P1WordExecution.State.write]

omit [DecidableEq V] in
theorem write_other (st : State V B) {r r' : Reg} (value : Word) (different : r' ≠ r) :
    (st.write r value).machine.registers r' = st.machine.registers r' := by
  simp [State.write, P1WordExecution.State.write, different]

theorem execute_branch_one (st : State V B) (c : Reg) (yes no : Source T)
    (one : st.machine.registers c = 1) : execute M st (.branch c yes no) = execute M st yes := by
  simp [executeWith, one]

theorem execute_branch_zero (st : State V B) (c : Reg) (yes no : Source T)
    (zero : st.machine.registers c = 0) : execute M st (.branch c yes no) = execute M st no := by
  simp [executeWith, zero]

omit [DecidableEq V] in
theorem continueLoop_one (st : State V B) (k : Reg) (next : State V B → Flow V B)
    (one : st.machine.registers k = 1) : continueLoop st (some k) next = next st := by
  simp [continueLoop, one]

omit [DecidableEq V] in
theorem continueLoop_zero (st : State V B) (k : Reg) (next : State V B → Flow V B)
    (zero : st.machine.registers k = 0) : continueLoop st (some k) next = .continuing st := by
  simp [continueLoop, zero]

theorem ofNat_toNat_of_lt {j : ℕ} (small : j < 2 ^ 64) : (BitVec.ofNat 64 j).toNat = j := by
  rw [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt small

theorem ofNat_succ (j : ℕ) : BitVec.ofNat 64 j + 1 = BitVec.ofNat 64 (j + 1) := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.add_mod]

/-- The matches of the remaining candidates of a premise's scan. -/
def candidateMatches (s : Store V) (role : Role) (pattern : T) (gs : List (Goal T)) (m : Match V B)
    (cands : List (ℕ × V)) : List (Match V B) :=
  cands.flatMap fun x =>
    match attempt M role pattern m x with
    | some m' => solve M s gs m'
    | none => []

/-- The loop body of a premise. -/
def premiseBody (cap : BitVec 32) (takes makes : ℕ) (role : Role) (pattern : T) (level : ℕ)
    (gs : List (Goal T)) : Source T :=
  .seq (.instruction (.transform (.premise role pattern level (indexReg level) testReg)))
    (.branch testReg (body cap takes makes (level + 1) gs) .skip)

/-- **A premise's choice point is an early-exit loop**: from index `j`, the loop finds the first match
of the remaining candidates, publishes it and stops, or ends with everything kept. -/
theorem loop_searched (cap : BitVec 32) (s : Store V) (capped : s.occurrences.length ≤ cap.toNat)
    (takes makes : ℕ) (role : Role) (pattern : T) (gs : List (Goal T)) (level : ℕ) (m : Match V B)
    (small : level ≤ 7)
    (inner : ∀ (m' : Match V B) (st₁ : State V B), Ready s (level + 1) m' st₁ →
      (∀ m'' ∈ solve M s gs m', m''.taken.length = takes ∧ m''.made.length = makes) →
      Searched s (level + 1) st₁ (solve M s gs m') (execute M st₁ (body cap takes makes (level + 1) gs)))
    (lengths : ∀ m'' ∈ candidateMatches M s role pattern gs m s.occurrences,
      m''.taken.length = takes ∧ m''.made.length = makes) :
    ∀ (r j : ℕ) (st : State V B), j + r = s.occurrences.length → Ready s level m st →
      st.machine.registers (indexReg level) = BitVec.ofNat 64 j →
      Searched s level st (candidateMatches M s role pattern gs m (s.occurrences.drop j))
        (loop (fun next => execute M next (premiseBody cap takes makes role pattern level gs))
          (indexReg level) (some flagReg) r st)
  | 0, j, st, sum, _, _ => by
      have empty : s.occurrences.drop j = [] := List.drop_eq_nil_of_le (by omega)
      rw [empty]
      exact ⟨st, rfl, Kept.refl level st⟩
  | r + 1, j, st, sum, ready, index => by
      have inside : j < s.occurrences.length := by omega
      have bounded : j < 2 ^ 64 := by have := cap.isLt; omega
      have xVal := indexReg_val small
      have dropped : s.occurrences.drop j = s.occurrences[j] :: s.occurrences.drop (j + 1) :=
        List.drop_eq_getElem_cons inside
      have occurrence : st.store.occurrences[(st.machine.registers (indexReg level)).toNat]? =
          some s.occurrences[j] := by
        rw [index, ofNat_toNat_of_lt bounded, ready.store]
        exact List.getElem?_eq_getElem inside
      -- the rest of the loop, after a candidate that leaves everything kept
      have advance : ∀ following : State V B, Kept level st following →
          following.machine.registers (indexReg level) = BitVec.ofNat 64 j →
          following.levels level = m →
          Searched s level st (candidateMatches M s role pattern gs m (s.occurrences.drop (j + 1)))
            (continueLoop following (some flagReg) fun next =>
              loop (fun next => execute M next (premiseBody cap takes makes role pattern level gs))
                (indexReg level) (some flagReg) r
                (next.write (indexReg level) (next.machine.registers (indexReg level) + 1))) := by
        intro following kept followingIndex followingLevel
        have flag : following.machine.registers flagReg = 1 := by
          rw [kept.registers flagReg (by simp [flagReg]; omega), ready.flag]
        rw [continueLoop_one following flagReg _ flag, followingIndex, ofNat_succ]
        let next := following.write (indexReg level) (BitVec.ofNat 64 (j + 1))
        have nextReady : Ready s level m next := by
          refine ⟨?_, followingLevel, ?_, ?_, ?_⟩
          · change following.store = s
            rw [kept.store, ready.store]
          · rw [write_other following _ (by simp [boundReg, indexReg, Fin.ext_iff]; omega),
              kept.registers boundReg (by simp [boundReg]; omega), ready.bound]
          · rw [write_other following _ (by simp [flagReg, indexReg, Fin.ext_iff]; omega), flag]
          · change following.machine.spent.toNat ≤ following.machine.budget.toNat
            rw [kept.spent, kept.budget]
            exact ready.funds
        have later := loop_searched cap s capped takes makes role pattern gs level m small inner lengths
          r (j + 1) next (by omega) nextReady (write_same following _ _)
        exact later.of_kept (kept.trans (Kept.write following _ _ (by omega)))
      simp only [loop]
      rw [continueLoop_one st flagReg _ ready.flag]
      simp only [premiseBody, execute_seq]
      rw [dropped]
      simp only [candidateMatches, List.flatMap_cons]
      cases tried : attempt M role pattern m s.occurrences[j] with
      | none =>
          have matched : execute M st (.instruction (.transform (.premise role pattern level (indexReg level) testReg))) =
              .continuing (st.write testReg 0) := by
            simp [executeWith, executeInstructionWith, P1Source.Instruction.view, StoreProfile.step, StoreProfile.ground, occurrence, ready.current, tried]
          rw [matched]
          simp only [Flow.thenContinue, List.nil_append]
          rw [execute_branch_zero M _ _ _ _ (write_same st testReg 0)]
          simp only [executeWith]
          exact advance (st.write testReg 0) (Kept.write st _ _ (by simp [testReg]; omega))
            (by rw [write_other st _ (by simp [testReg, indexReg, Fin.ext_iff]; omega), index])
            ready.current
      | some m' =>
          let st₁ := (st.setLevel (level + 1) m').write testReg 1
          have matched : execute M st (.instruction (.transform (.premise role pattern level (indexReg level) testReg))) =
              .continuing st₁ := by
            simp [executeWith, executeInstructionWith, P1Source.Instruction.view, StoreProfile.step, StoreProfile.ground, occurrence, ready.current, tried, st₁]
          rw [matched]
          simp only [Flow.thenContinue]
          rw [execute_branch_one M _ _ _ _ (write_same _ testReg 1)]
          have ready₁ : Ready s (level + 1) m' st₁ := by
            refine ⟨ready.store, ?_, ?_, ?_, ready.funds⟩
            · simp [st₁, State.write, State.setLevel]
            · rw [write_other _ _ (by simp [boundReg, testReg])]
              exact ready.bound
            · rw [write_other _ _ (by simp [flagReg, testReg])]
              exact ready.flag
          have kept₁ : Kept level st st₁ :=
            (Kept.setLevel st (level + 1) m' (by omega)).trans
              (Kept.write _ testReg 1 (by simp [testReg]; omega))
          have innerLengths : ∀ m'' ∈ solve M s gs m', m''.taken.length = takes ∧ m''.made.length = makes := by
            intro m'' member
            apply lengths m''
            simp only [candidateMatches, List.mem_flatMap]
            exact ⟨s.occurrences[j], List.getElem_mem inside, by rw [tried]; exact member⟩
          have searched := inner m' st₁ ready₁ innerLengths
          cases found : solve M s gs m' with
          | nil =>
              rw [found] at searched
              obtain ⟨after, flowing, kept⟩ := searched
              rw [flowing]
              simp only [List.nil_append]
              have index₁ : after.machine.registers (indexReg level) = BitVec.ofNat 64 j := by
                rw [kept.registers _ (by omega), write_other _ _ (by simp [testReg, indexReg, Fin.ext_iff]; omega)]
                exact index
              have level₁ : after.levels level = m := by
                rw [kept.levels level (by omega)]
                simp [st₁, State.write, State.setLevel, ready.current]
              exact advance after (kept₁.trans (kept.mono (by omega))) index₁ level₁
          | cons first rest =>
              rw [found] at searched
              simp only [List.cons_append]
              rcases searched with ⟨paying, after, flowing, published⟩ | ⟨broke, payload, after, flowing, unpaid⟩
              · rw [flowing]
                simp only
                rw [continueLoop_zero after flagReg _ published.flag]
                refine .inl ⟨by rw [← kept₁.spent, ← kept₁.budget]; exact paying, after, rfl, ?_⟩
                exact ⟨published.store, published.flag, published.spent.trans (by rw [kept₁.spent]),
                  published.budget.trans kept₁.budget, published.regions.trans kept₁.regions,
                  published.frame.trans kept₁.frame, published.memory.trans kept₁.memory⟩
              · rw [flowing]
                simp only
                refine .inr ⟨by rw [← kept₁.spent, ← kept₁.budget]; exact broke, payload, after, rfl, ?_⟩
                exact ⟨unpaid.store, unpaid.spent.trans kept₁.spent, unpaid.budget.trans kept₁.budget,
                  unpaid.regions.trans kept₁.regions, unpaid.frame.trans kept₁.frame,
                  unpaid.memory.trans kept₁.memory⟩

/-- **The code of a rule's goals realizes their search**: from a ready state it finds the first
match the evaluator lists, publishes it and pays, or ends exhausted, or continues with everything
kept when there is none. -/
theorem body_searched (cap : BitVec 32) (s : Store V) (capped : s.occurrences.length ≤ cap.toNat)
    (takes makes : ℕ) :
    ∀ (gs : List (Goal T)) (level : ℕ) (m : Match V B) (st : State V B),
      level + premiseCount gs ≤ 8 → Ready s level m st →
      (∀ m' ∈ solve M s gs m, m'.taken.length = takes ∧ m'.made.length = makes) →
      Searched s level st (solve M s gs m) (execute M st (body cap takes makes level gs))
  | [], level, m, st, _, ready, lengths => by
      obtain ⟨takeLength, madeLength⟩ := lengths m (by simp [solve])
      simp only [body, solve]
      rw [← takeLength, ← madeLength]
      exact publication_searched M s level m st ready
  | .determinate d :: gs, level, m, st, small, ready, lengths => by
      have premises : level + premiseCount gs ≤ 8 := by simpa [premiseCount] using small
      simp only [body, execute_seq]
      cases applied : d.apply M s m with
      | none =>
          have tested : execute M st (.instruction (.transform (.test d level testReg))) =
              .continuing (st.write testReg 0) := by
            simp [executeWith, executeInstructionWith, P1Source.Instruction.view, StoreProfile.step, StoreProfile.ground, ready.store, ready.current, applied]
          rw [tested]
          simp only [Flow.thenContinue]
          rw [execute_branch_zero M _ _ _ _ (write_same st testReg 0)]
          have empty : solve M s (.determinate d :: gs) m = [] := by simp [solve, applied]
          rw [empty]
          exact ⟨_, rfl, Kept.write st testReg 0 (by simp [testReg]; omega)⟩
      | some m' =>
          let st₁ := (st.setLevel level m').write testReg 1
          have tested : execute M st (.instruction (.transform (.test d level testReg))) =
              .continuing st₁ := by
            simp [executeWith, executeInstructionWith, P1Source.Instruction.view, StoreProfile.step, StoreProfile.ground, ready.store, ready.current, applied, st₁]
          rw [tested]
          simp only [Flow.thenContinue]
          rw [execute_branch_one M _ _ _ _ (write_same _ testReg 1)]
          have same : solve M s (.determinate d :: gs) m = solve M s gs m' := by simp [solve, applied]
          rw [same]
          have ready₁ : Ready s level m' st₁ := by
            refine ⟨ready.store, ?_, ?_, ?_, ready.funds⟩
            · simp [st₁, State.write, State.setLevel]
            · rw [write_other _ _ (by simp [boundReg, testReg])]
              exact ready.bound
            · rw [write_other _ _ (by simp [flagReg, testReg])]
              exact ready.flag
          have kept₁ : Kept level st st₁ :=
            (Kept.setLevel st level m' le_rfl).trans (Kept.write _ testReg 1 (by simp [testReg]; omega))
          exact (body_searched cap s capped takes makes gs level m' st₁ premises ready₁
            (by rw [← same]; exact lengths)).of_kept kept₁
  | .premise role pattern :: gs, level, m, st, small, ready, lengths => by
      have premises : level + 1 + premiseCount gs ≤ 8 := by simp [premiseCount] at small; omega
      have levelSmall : level ≤ 7 := by simp [premiseCount] at small; omega
      have bounded : s.occurrences.length < 2 ^ 64 := by have := cap.isLt; omega
      have notCapped : ¬ cap.toNat < (st.machine.registers boundReg).toNat := by
        rw [ready.bound, ofNat_toNat_of_lt bounded]
        omega
      have whole : solve M s (.premise role pattern :: gs) m =
          candidateMatches M s role pattern gs m (s.occurrences.drop 0) := rfl
      change Searched s level st (solve M s (.premise role pattern :: gs) m)
        (if cap.toNat < (st.machine.registers boundReg).toNat then fail .unsupported st
          else loop (fun next => execute M next (premiseBody cap takes makes role pattern level gs))
            (indexReg level) (some flagReg) (st.machine.registers boundReg).toNat
            (st.write (indexReg level) 0))
      rw [if_neg notCapped, ready.bound, ofNat_toNat_of_lt bounded, whole]
      have xVal := indexReg_val levelSmall
      have ready₀ : Ready s level m (st.write (indexReg level) 0) := by
        refine ⟨ready.store, ready.current, ?_, ?_, ready.funds⟩
        · rw [write_other _ _ (by simp [boundReg, indexReg, Fin.ext_iff]; omega)]
          exact ready.bound
        · rw [write_other _ _ (by simp [flagReg, indexReg, Fin.ext_iff]; omega)]
          exact ready.flag
      have looped := loop_searched M cap s capped takes makes role pattern gs level m levelSmall
        (fun m' st₁ ready₁ lengths₁ =>
          body_searched cap s capped takes makes gs (level + 1) m' st₁ premises ready₁ lengths₁)
        (fun m'' member => lengths m'' (by rw [whole]; simpa using member))
        s.occurrences.length 0 _ (by simp) ready₀ (write_same st _ 0)
      exact looped.of_kept (Kept.write st _ _ (by omega))

/-! ## The program -/

/-- The parts of a state a run leaves observable agree: the store, the receipt, the allowance,
the regions, the frame and the memory. -/
structure Agrees (before after : State V B) : Prop where
  store : after.store = before.store
  spent : after.machine.spent = before.machine.spent
  budget : after.machine.budget = before.machine.budget
  regions : after.machine.regions = before.machine.regions
  frame : after.machine.frame = before.machine.frame
  memory : after.machine.memory = before.machine.memory

omit [DecidableEq V] in
theorem Agrees.trans {a b c : State V B} (first : Agrees a b) (second : Agrees b c) : Agrees a c :=
  ⟨second.store.trans first.store, second.spent.trans first.spent, second.budget.trans first.budget,
    second.regions.trans first.regions, second.frame.trans first.frame, second.memory.trans first.memory⟩

omit [DecidableEq V] in
theorem Kept.agrees {level : ℕ} {before after : State V B} (kept : Kept level before after) :
    Agrees before after :=
  ⟨kept.store, kept.spent, kept.budget, kept.regions, kept.frame, kept.memory⟩

/-- **What one invocation does**, given the firings the evaluator lists: with none it returns
`REFUSED` with everything kept; with some, it returns `FIRED` with the first published and paid, or
`EXHAUSTED` with nothing done when no unit is left. -/
def Fired (s : Store V) (before : State V B) : List (Rule T × Match V B) → Flow V B → Prop
  | [], flow => ∃ payload after, flow = .returned .refused payload after ∧ Unpaid s before after
  | f :: _, flow =>
      (before.machine.spent.toNat < before.machine.budget.toNat ∧
        ∃ payload after, flow = .returned .completed payload after ∧ Published s f.2 before after) ∨
      (before.machine.budget.toNat ≤ before.machine.spent.toNat ∧
        ∃ payload after, flow = .returned .exhausted payload after ∧ Unpaid s before after)

omit [DecidableEq V] in
theorem Fired.of_agrees {s : Store V} {st st' : State V B} (agrees : Agrees st st') :
    ∀ {L : List (Rule T × Match V B)} {flow : Flow V B}, Fired s st' L flow → Fired s st L flow
  | [], _, ⟨payload, after, flowing, nothing⟩ =>
      ⟨payload, after, flowing, nothing.store, nothing.spent.trans agrees.spent,
        nothing.budget.trans agrees.budget, nothing.regions.trans agrees.regions,
        nothing.frame.trans agrees.frame, nothing.memory.trans agrees.memory⟩
  | _ :: _, _, .inl ⟨paying, payload, after, flowing, published⟩ => by
      refine .inl ⟨?_, payload, after, flowing, ?_⟩
      · rw [← agrees.spent, ← agrees.budget]; exact paying
      · exact ⟨published.store, published.flag, published.spent.trans (by rw [agrees.spent]),
          published.budget.trans agrees.budget, published.regions.trans agrees.regions,
          published.frame.trans agrees.frame, published.memory.trans agrees.memory⟩
  | _ :: _, _, .inr ⟨broke, payload, after, flowing, nothing⟩ => by
      refine .inr ⟨?_, payload, after, flowing, ?_⟩
      · rw [← agrees.spent, ← agrees.budget]; exact broke
      · exact ⟨nothing.store, nothing.spent.trans agrees.spent, nothing.budget.trans agrees.budget,
          nothing.regions.trans agrees.regions, nothing.frame.trans agrees.frame,
          nothing.memory.trans agrees.memory⟩

/-- The matches of a rule have one taken occurrence per take pattern and one made value per produced
term. -/
theorem solve_goals_lengths (s : Store V) (r : Rule T) (m : Match V B)
    (member : m ∈ solve M s (goals r) (Match.start M)) :
    m.taken.length = r.body.take.length ∧ m.made.length = r.body.produce.length := by
  obtain ⟨xs, ys, m₁, m₂, _, _, takes, reads, dets⟩ := (mem_solve_goals s r m).mp member
  obtain ⟨takenEq, _, _, madeEq₁, _, _⟩ := attemptAll_take r.body.take _ m₁ xs takes
  obtain ⟨_, takenEq₂, _, madeEq₂, _⟩ := attemptAll_read r.body.read m₁ m₂ ys reads
  obtain ⟨_, _, cs, ws, _, wsRel, rfl⟩ := (applyAll_determinates_iff s r m₂ m).mp dets
  constructor
  · change m₂.taken.length = _
    rw [takenEq₂, takenEq, attemptAll_length .take r.body.take _ m₁ xs takes]
    simp [Match.start]
  · change (m₂.made ++ ws).length = _
    rw [madeEq₂, madeEq₁, wsRel.length_eq]
    simp [Match.start]

omit [DecidableEq V] in
theorem premiseCount_goals (r : Rule T) :
    premiseCount (goals r) = r.body.take.length + r.body.read.length := by
  have count : ∀ (gs : List (Goal T)) (ds : List (Determinate T)),
      premiseCount (gs ++ ds.map Goal.determinate) = premiseCount gs := by
    intro gs ds
    induction gs with
    | nil =>
        induction ds with
        | nil => rfl
        | cons d ds ih => simpa [premiseCount] using ih
    | cons g gs ih => cases g <;> simp [premiseCount, ih]
  have premises : ∀ (role : Role) (ps : List T) (rest : List (Goal T)),
      premiseCount (ps.map (Goal.premise role) ++ rest) = ps.length + premiseCount rest := by
    intro role ps rest
    induction ps with
    | nil => simp
    | cons p ps ih => simp [premiseCount, ih]; omega
  rw [goals_eq, count, premises, ← List.append_nil (r.body.read.map _), premises]
  simp [premiseCount]

/-- **The rule blocks realize the program's search.** -/
theorem rules_fired (cap : BitVec 32) (s : Store V) (capped : s.occurrences.length ≤ cap.toNat) :
    ∀ (P : List (Rule T)) (st : State V B),
      (∀ r ∈ P, r.body.take.length + r.body.read.length ≤ 8) → st.store = s →
      st.machine.registers boundReg = BitVec.ofNat 64 s.occurrences.length →
      st.machine.registers flagReg = 1 → st.machine.spent.toNat ≤ st.machine.budget.toNat →
      Fired s st (firings M P s) (execute M st (rulesCode cap P))
  | [], st, _, store, _, _, _ =>
      ⟨_, st, rfl, store, rfl, rfl, rfl, rfl, rfl⟩
  | r :: rs, st, small, store, bound, flag, funds => by
      simp only [rulesCode, ruleBlock, execute_seq]
      let st₀ := st.setLevel 0 (Match.start M)
      have opened : execute M st (.instruction (.transform (.open 0))) = .continuing st₀ := rfl
      rw [opened]
      simp only [Flow.thenContinue]
      have ready₀ : Ready s 0 (Match.start M) st₀ := by
        refine ⟨store, ?_, bound, flag, funds⟩
        simp [st₀, State.setLevel]
      have searched := body_searched M cap s capped r.body.take.length r.body.produce.length
        (goals r) 0 (Match.start M) st₀
        (by rw [premiseCount_goals]; simpa using small r List.mem_cons_self) ready₀
        (fun m' member => solve_goals_lengths M s r m' member)
      have split : firings M (r :: rs) s =
          (solve M s (goals r) (Match.start M)).map (fun m => (r, m)) ++ firings M rs s := by
        simp [firings]
      rw [split]
      have agrees₀ : Agrees st st₀ := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
      cases found : solve M s (goals r) (Match.start M) with
      | nil =>
          rw [found] at searched
          obtain ⟨after, flowing, kept⟩ := searched
          rw [flowing]
          simp only [List.map_nil, List.nil_append]
          have afterFlag : after.machine.registers flagReg = 1 := by
            rw [kept.registers flagReg (by simp [flagReg])]
            exact flag
          rw [execute_branch_one M _ _ _ _ afterFlag]
          have later := rules_fired cap s capped rs after
            (fun r' member => small r' (List.mem_cons_of_mem _ member))
            (by rw [kept.store]; exact store)
            (by rw [kept.registers boundReg (by simp [boundReg])]; exact bound) afterFlag
            (by rw [kept.spent, kept.budget]; exact funds)
          exact later.of_agrees (agrees₀.trans kept.agrees)
      | cons first rest =>
          rw [found] at searched
          simp only [List.map_cons, List.cons_append]
          rcases searched with ⟨paying, after, flowing, published⟩ | ⟨broke, payload, after, flowing, nothing⟩
          · rw [flowing]
            simp only
            have zero : after.machine.registers flagReg = 0 := published.flag
            rw [execute_branch_zero M _ _ _ _ zero]
            exact Fired.of_agrees agrees₀ (L := (r, first) :: _) (.inl ⟨paying, _, after, rfl, published⟩)
          · rw [flowing]
            simp only
            exact Fired.of_agrees agrees₀ (L := (r, first) :: _) (.inr ⟨broke, payload, after, rfl, nothing⟩)

/-- **The compiled firing loop realizes one firing of the evaluator**: `REFUSED` when it finds no
firing, `FIRED` with the first firing published and one unit paid, or `EXHAUSTED` with nothing done
when no unit is left. -/
theorem program_fires (cap : BitVec 32) (P : List (Rule T)) (st : State V B)
    (capped : st.store.occurrences.length ≤ cap.toNat)
    (funds : st.machine.spent.toNat ≤ st.machine.budget.toNat)
    (small : ∀ r ∈ P, r.body.take.length + r.body.read.length ≤ 8) :
    Fired st.store st (firings M P st.store) (execute M st (program cap P)) := by
  rw [program, execute_seq, execute_immediate]
  simp only [Flow.thenContinue]
  rw [execute_seq]
  let st₁ := st.write flagReg 1
  let st₂ := st₁.write boundReg (BitVec.ofNat 64 st₁.store.occurrences.length)
  have sized : execute M st₁ (.instruction (.transform (.size boundReg))) = .continuing st₂ := rfl
  rw [sized]
  simp only [Flow.thenContinue]
  have fired := rules_fired M cap st.store capped P st₂ small rfl (write_same st₁ _ _)
    (by rw [write_other st₁ _ (by simp [flagReg, boundReg])]; exact write_same st _ _) funds
  exact Fired.of_agrees (st := st) (st' := st₂) ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ fired

/-- The units left to pay. -/
def allowance (st : State V B) : ℕ := st.machine.budget.toNat - st.machine.spent.toNat

/-- **One invocation of the compiled program is one search-and-firing of the derived machine**, from
the same store with the remaining allowance: it returns `REFUSED` exactly where the machine halts
quiescent, `EXHAUSTED` exactly where it halts exhausted, and otherwise returns `FIRED` with the store
and the allowance of the machine's next search. -/
theorem program_simulates_machine (cap : BitVec 32) (P : List (Rule T)) (st : State V B)
    (capped : st.store.occurrences.length ≤ cap.toNat)
    (funds : st.machine.spent.toNat ≤ st.machine.budget.toNat)
    (small : ∀ r ∈ P, r.body.take.length + r.body.read.length ≤ 8) :
    (∃ payload after, execute M st (program cap P) = .returned .refused payload after ∧
        Unpaid st.store st after ∧
        Steps M P (.run (allowance st) st.store) (.halt (.quiescent st.store))) ∨
    (∃ payload after, execute M st (program cap P) = .returned .exhausted payload after ∧
        Unpaid st.store st after ∧ allowance st = 0 ∧
        Steps M P (.run (allowance st) st.store) (.halt (.exhausted st.store))) ∨
    (∃ (a : ℕ) (payload : Word) (after : State V B),
        execute M st (program cap P) = .returned .completed payload after ∧
        allowance st = a + 1 ∧ allowance after = a ∧
        after.machine.budget = st.machine.budget ∧ after.machine.memory = st.machine.memory ∧
        Steps M P (.run (allowance st) st.store) (.run a after.store)) := by
  have fired := program_fires M cap P st capped funds small
  cases first : firings M P st.store with
  | nil =>
      rw [first] at fired
      obtain ⟨payload, after, flowing, nothing⟩ := fired
      left
      refine ⟨payload, after, flowing, nothing, ?_⟩
      exact (machine_run_iff M P _ _ _).mpr (run_quiescent M P _ _ first).symm
  | cons f rest =>
      rw [first] at fired
      rcases fired with ⟨paying, payload, after, flowing, published⟩ | ⟨broke, payload, after, flowing, nothing⟩
      · right; right
        have positive : allowance st = (allowance st - 1) + 1 := by unfold allowance; omega
        have spentAfter : after.machine.spent.toNat = st.machine.spent.toNat + 1 := by
          rw [published.spent, BitVec.toNat_add_of_lt]
          · rfl
          · have := st.machine.budget.isLt
            change st.machine.spent.toNat + 1 < 2 ^ 64
            omega
        refine ⟨allowance st - 1, payload, after, flowing, positive, ?_, published.budget, published.memory, ?_⟩
        · unfold allowance
          rw [spentAfter, published.budget]
          omega
        · rw [positive, published.store]
          exact search_commits M P _ st.store f rest first
      · right; left
        have zero : allowance st = 0 := by unfold allowance; omega
        refine ⟨payload, after, flowing, nothing, zero, ?_⟩
        rw [zero]
        exact (machine_run_iff M P _ _ _).mpr (run_zero_fire M P _ f rest first).symm

/-! ## Runs: one invocation per firing -/

/-- **Invoke the compiled program once per firing**, from the state each invocation returns, at most
`fuel` times. -/
def invoke (cap : BitVec 32) (P : List (Rule T)) : ℕ → State V B → Flow V B
  | 0, st => .continuing st
  | n + 1, st =>
      match execute M st (program cap P) with
      | .returned .completed _ after => invoke cap P n after
      | flow => flow

/-- The stores a run passes through. -/
def runStores (P : List (Rule T)) : ℕ → Store V → List (Store V)
  | 0, s => [s]
  | a + 1, s =>
      match firings M P s with
      | [] => [s]
      | f :: _ => s :: runStores P a (publish s f.2)

/-- **Invoked once per firing, the compiled program realizes the run**: with the allowance of the
run, it ends `REFUSED` at the run's quiescent store, or `EXHAUSTED` at the store where the allowance
ran out, within one invocation more than the allowance. -/
theorem invoke_run (cap : BitVec 32) (P : List (Rule T))
    (small : ∀ r ∈ P, r.body.take.length + r.body.read.length ≤ 8) :
    ∀ (a : ℕ) (st : State V B), allowance st = a →
      st.machine.spent.toNat ≤ st.machine.budget.toNat →
      (∀ s' ∈ runStores M P a st.store, s'.occurrences.length ≤ cap.toNat) →
      match run M P a st.store with
      | .quiescent s' => ∃ payload after,
          invoke M cap P (a + 1) st = .returned .refused payload after ∧ after.store = s'
      | .exhausted s' => ∃ payload after,
          invoke M cap P (a + 1) st = .returned .exhausted payload after ∧ after.store = s'
  | a, st, allowed, funds, capped => by
      have fired := program_fires M cap P st (capped st.store (by cases a <;> simp [runStores]; split <;> simp)) funds small
      cases first : firings M P st.store with
      | nil =>
          rw [first] at fired
          obtain ⟨payload, after, flowing, nothing⟩ := fired
          rw [run_quiescent M P a st.store first]
          refine ⟨payload, after, ?_, nothing.store⟩
          simp only [invoke, flowing]
      | cons f rest =>
          rw [first] at fired
          rcases fired with ⟨paying, payload, after, flowing, published⟩ | ⟨broke, payload, after, flowing, nothing⟩
          · cases a with
            | zero => unfold allowance at allowed; omega
            | succ a' =>
                rw [run_succ_fire M P a' st.store f rest first]
                have spentAfter : after.machine.spent.toNat = st.machine.spent.toNat + 1 := by
                  rw [published.spent, BitVec.toNat_add_of_lt]
                  · rfl
                  · have := st.machine.budget.isLt
                    change st.machine.spent.toNat + 1 < 2 ^ 64
                    omega
                have later := invoke_run cap P small a' after
                  (by unfold allowance at allowed ⊢; rw [spentAfter, published.budget]; omega)
                  (by rw [spentAfter, published.budget]; omega)
                  (fun s' member => capped s' (by
                    rw [published.store] at member
                    simp only [runStores, first]
                    exact List.mem_cons_of_mem _ member))
                rw [published.store] at later
                have unfolded : invoke M cap P (a' + 1 + 1) st = invoke M cap P (a' + 1) after := by
                  simp only [invoke, flowing]
                rw [unfolded]
                exact later
          · have zero : a = 0 := by unfold allowance at allowed; omega
            subst zero
            rw [run_zero_fire M P st.store f rest first]
            refine ⟨payload, after, ?_, nothing.store⟩
            simp only [invoke, flowing]

/-- **Invoked once per firing, the compiled program realizes the derived machine's run**: where the
machine halts quiescent, the invocations end `REFUSED` with the same store. -/
theorem invoke_simulates_quiescent (cap : BitVec 32) (P : List (Rule T))
    (small : ∀ r ∈ P, r.body.take.length + r.body.read.length ≤ 8) (st : State V B)
    (funds : st.machine.spent.toNat ≤ st.machine.budget.toNat)
    (capped : ∀ s' ∈ runStores M P (allowance st) st.store, s'.occurrences.length ≤ cap.toNat)
    (s' : Store V) (halts : Steps M P (.run (allowance st) st.store) (.halt (.quiescent s'))) :
    ∃ payload after,
      invoke M cap P (allowance st + 1) st = .returned .refused payload after ∧ after.store = s' := by
  have same := (machine_run_iff M P _ _ _).mp halts
  have realized := invoke_run M cap P small (allowance st) st rfl funds capped
  rw [← same] at realized
  exact realized

/-- Where the machine halts exhausted, the invocations end `EXHAUSTED` with the same store. -/
theorem invoke_simulates_exhausted (cap : BitVec 32) (P : List (Rule T))
    (small : ∀ r ∈ P, r.body.take.length + r.body.read.length ≤ 8) (st : State V B)
    (funds : st.machine.spent.toNat ≤ st.machine.budget.toNat)
    (capped : ∀ s' ∈ runStores M P (allowance st) st.store, s'.occurrences.length ≤ cap.toNat)
    (s' : Store V) (halts : Steps M P (.run (allowance st) st.store) (.halt (.exhausted s'))) :
    ∃ payload after,
      invoke M cap P (allowance st + 1) st = .returned .exhausted payload after ∧ after.store = s' := by
  have same := (machine_run_iff M P _ _ _).mp halts
  have realized := invoke_run M cap P small (allowance st) st rfl funds capped
  rw [← same] at realized
  exact realized

end Search

end Mettapedia.Machines.TIsa.StoreInstructions
