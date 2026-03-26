-- LLM primer: This defines the MM2 worklist machine for memoized recursive evaluation.
-- Each MachineState constructor corresponds to one kind of MM2/MORK fact.
-- The MachineStep relation defines valid transitions (one per MM2 exec rule type).
-- The machine refines evalMemo: if the machine produces (done 0 v), then EvalSem node v.
--
-- Scoping: this is a fib-scoped PoC validating the inflight/waiter/memo/driver pattern
-- on integer-arg calls. Generic CBV arg-evaluation and join frames come later.
--
-- Council: Martin-Löf/Coquand (machine as inductive relation),
--   Meredith/Stay (1:1 with MM2 facts), Carneiro (reuse EvalIR types),
--   Knuth/Tao (fib-scoped, don't over-generalize).

import MeTTailCore.EvalIR

namespace MeTTailCore.EvalIRMachine

open MeTTailCore.EvalIR

-- ═══════════════════════════════════════════════════════════════════════════
-- § Machine State: Each constructor = one kind of MM2 fact
-- ═══════════════════════════════════════════════════════════════════════════

/-- A request ID: uniquely identifies a call site (not the canonical call). -/
abbrev ReqId := Nat

/-- A canonical call key: the function head + evaluated argument values.
    For the fib PoC, args are always integer literals, so EvalNode suffices.
    For the generic machine, this would be (String × List EvalValue). -/
structure CallKey where
  head : String
  args : List EvalValue
deriving DecidableEq, Repr

/-- Machine state facts. Each constructor corresponds to one kind of MM2/MORK atom.
    Persistent facts (inflight, memo) are never consumed by transitions.
    Consumable facts (need, waiting, open, active, driverReady, done) are
    removed by the transition that matches them. -/
inductive Fact where
  | need        : ReqId → CallKey → Fact         -- (need REQ CALL): request needs evaluation
  | waiting     : ReqId → CallKey → Fact         -- (waiting REQ CALL): blocked on CALL
  | done        : ReqId → EvalValue → Fact       -- (done REQ VAL): request answered
  | inflight    : CallKey → Fact                  -- (inflight CALL): persistent claim
  | open        : CallKey → Fact                  -- (open CALL): ready for driver
  | memo        : CallKey → EvalValue → Fact      -- (memo CALL VAL): persistent cache
  | active      : CallKey → Fact                  -- (active CALL): being computed
  | driverReady : Fact                             -- (driver ready): scheduling token
deriving DecidableEq, Repr

/-- A machine configuration: a list of facts (modeling MORK's atom space).
    In the real MM2, this is an unordered multiset; List suffices for the PoC. -/
abbrev Config := List Fact

/-- Check membership in a configuration. -/
def Config.has (c : Config) (f : Fact) : Prop := f ∈ c

/-- Remove one occurrence of a fact from the configuration. -/
def Config.remove (c : Config) (f : Fact) : Config := c.erase f

/-- Add a fact to the configuration. -/
def Config.add (c : Config) (f : Fact) : Config := f :: c

-- ═══════════════════════════════════════════════════════════════════════════
-- § Machine Transitions: Each constructor = one MM2 exec rule type
-- ═══════════════════════════════════════════════════════════════════════════
-- All transitions use positive matching only (no negation).
-- Priority ordering ensures correct dispatch:
--   P0 memo-hit > P1 attach-waiter > P2 first-claim > P3 driver-select > P4 compute > P5 discharge

/-- One step of the worklist machine.
    Parameterized by the program's rewrite rules. -/
inductive Step (rules : List EvalRule) : Config → Config → Prop where

  /-- P0 — Memo hit: if (need req call) and (memo call val) exist,
      produce (done req val) and consume (need req call).
      The (memo call val) is NOT consumed (persistent). -/
  | memoHit (req : ReqId) (call : CallKey) (val : EvalValue) (cfg : Config) :
      .need req call ∈ cfg →
      .memo call val ∈ cfg →
      Step rules cfg
        (cfg.remove (.need req call) |>.add (.done req val))

  /-- P1 — Attach waiter: if (need req call) and (inflight call) exist,
      convert need to waiting. (inflight call) is NOT consumed (persistent). -/
  | attachWaiter (req : ReqId) (call : CallKey) (cfg : Config) :
      .need req call ∈ cfg →
      .inflight call ∈ cfg →
      Step rules cfg
        (cfg.remove (.need req call) |>.add (.waiting req call))

  /-- P2 — First claim: if (need req call) exists and neither memo nor inflight
      for this call exist (ensured by priority ordering — P0 and P1 fire first),
      create inflight + open + waiting. -/
  | firstClaim (req : ReqId) (call : CallKey) (cfg : Config) :
      .need req call ∈ cfg →
      Step rules cfg
        (cfg.remove (.need req call)
         |>.add (.inflight call)
         |>.add (.open call)
         |>.add (.waiting req call))

  /-- P3 — Driver select: pick one open call, make it active.
      Consumes (driver ready) to ensure only one active at a time. -/
  | driverSelect (call : CallKey) (cfg : Config) :
      .driverReady ∈ cfg →
      .open call ∈ cfg →
      Step rules cfg
        (cfg.remove .driverReady |>.remove (.open call) |>.add (.active call))

  /-- P4 — Base case: (active (fib 0)) or (active (fib 1)) resolves directly.
      Produces (memo call val) and returns the driver token. -/
  | baseCase (call : CallKey) (val : EvalValue) (cfg : Config) :
      .active call ∈ cfg →
      -- The base case is determined by the program rules + eval semantics
      EvalSem rules (.userCall call.head (call.args.map EvalValue.toNode)) val →
      -- No child calls needed (base cases evaluate without recursion)
      Step rules cfg
        (cfg.remove (.active call)
         |>.add (.memo call val)
         |>.add .driverReady)

  /-- P4 — Expand: (active call) creates child (need ...) facts for sub-calls.
      This is function-specific. For fib(n) with n ≥ 2:
      creates need for fib(n-1) and fib(n-2), plus a join-wait frame.
      Consumes (active call), does NOT return driver token yet
      (children must complete first). -/
  | expand (call : CallKey) (childCalls : List CallKey)
           (nextReqId : Nat) (cfg : Config) :
      .active call ∈ cfg →
      -- childCalls are the sub-calls needed (e.g., [fib(n-1), fib(n-2)])
      -- childNeeds: the (need reqId childCall) facts to emit
      (childNeeds : List (ReqId × CallKey)) →
      Step rules cfg
        (cfg.remove (.active call)
         |> fun c => childNeeds.foldl (fun c ⟨rid, child⟩ => c.add (.need rid child)) c)

  /-- P5 — Waiter discharge: when (memo call val) exists and (waiting req call) exists,
      produce (done req val). (memo call val) is NOT consumed. -/
  | discharge (req : ReqId) (call : CallKey) (val : EvalValue) (cfg : Config) :
      .memo call val ∈ cfg →
      .waiting req call ∈ cfg →
      Step rules cfg
        (cfg.remove (.waiting req call) |>.add (.done req val))

-- ═══════════════════════════════════════════════════════════════════════════
-- § Reachability and Soundness
-- ═══════════════════════════════════════════════════════════════════════════

/-- Multi-step reachability: zero or more transitions. -/
inductive Reaches (rules : List EvalRule) : Config → Config → Prop where
  | refl : Reaches rules cfg cfg
  | step : Step rules cfg₁ cfg₂ → Reaches rules cfg₂ cfg₃ → Reaches rules cfg₁ cfg₃

/-- The initial configuration for evaluating a call. -/
def initialConfig (call : CallKey) : Config :=
  [.need 0 call, .driverReady]

/-- Configuration invariant: every memo and done fact is semantically correct.
    "Memo-sound" means: if (memo call val) is in cfg, then EvalSem for that call.
    "Done-sound" means: if (done req val) is in cfg, then val came from a sound memo. -/
def MemoSound (rules : List EvalRule) (cfg : Config) : Prop :=
  ∀ call val, .memo call val ∈ cfg →
    EvalSem rules (.userCall call.head (call.args.map EvalValue.toNode)) val

/-- The initial configuration has no memo facts, so MemoSound holds vacuously. -/
theorem memoSound_initial (call : CallKey) :
    MemoSound rules (initialConfig call) := by
  intro c v hmem; simp [initialConfig, List.mem_cons] at hmem

/-- Helper: .memo is preserved through List.erase of non-memo facts. -/
private theorem memo_mem_erase_of_ne {call : CallKey} {val : EvalValue} {f : Fact} {cfg : Config}
    (hmem : Fact.memo call val ∈ cfg) (hne : Fact.memo call val ≠ f) :
    Fact.memo call val ∈ cfg.erase f :=
  List.mem_erase_of_ne hne |>.mpr hmem

/-- Helper: .memo survives prepending a non-memo fact. -/
private theorem memo_mem_cons {call : CallKey} {val : EvalValue} {f : Fact} {cfg : Config}
    (hmem : Fact.memo call val ∈ cfg) :
    Fact.memo call val ∈ f :: cfg :=
  List.mem_cons_of_mem f hmem

/-- Helper: if .memo is in the result of foldl that only adds .need facts,
    then .memo was in the accumulator (because .need ≠ .memo). -/
private theorem memo_mem_of_foldl_need {call : CallKey} {val : EvalValue}
    {acc : Config} {needs : List (ReqId × CallKey)}
    (hmem : Fact.memo call val ∈ needs.foldl (fun c ⟨rid, child⟩ => c.add (.need rid child)) acc) :
    Fact.memo call val ∈ acc := by
  induction needs generalizing acc with
  | nil => exact hmem
  | cons head rest ih =>
    simp [List.foldl] at hmem
    have := ih hmem
    -- this : .memo call val ∈ (.need ...) :: acc
    cases List.mem_cons.mp this with
    | inl h => cases h  -- .need ≠ .memo
    | inr h => exact h

/-- Helper: .memo survives foldl that only adds .need facts. -/
private theorem memo_mem_foldl_need {call : CallKey} {val : EvalValue}
    {acc : Config} {needs : List (ReqId × CallKey)}
    (hmem : Fact.memo call val ∈ acc) :
    Fact.memo call val ∈ needs.foldl (fun c ⟨rid, child⟩ => c.add (.need rid child)) acc := by
  induction needs generalizing acc with
  | nil => exact hmem
  | cons head rest ih =>
    simp [List.foldl]
    apply ih
    exact List.mem_cons_of_mem _ hmem

/-- MemoSound is preserved by every Step transition.
    Key insight: the only Step that adds a .memo fact is baseCase,
    and that one carries EvalSem as a hypothesis. -/
theorem memoSound_step {rules : List EvalRule} {cfg cfg' : Config}
    (hInv : MemoSound rules cfg)
    (hStep : Step rules cfg cfg') :
    MemoSound rules cfg' := by
  intro call val hmem
  -- For each Step, show .memo call val was either already in cfg or is the baseCase's new entry.
  cases hStep with
  | memoHit req call' val' _ hNeed hMemo =>
    -- cfg' = (done req val') :: cfg.erase (need req call')
    -- .memo call val ∈ cfg' means it's either (done ...) [impossible] or in cfg.erase
    simp only [Config.add, Config.remove] at hmem
    cases List.mem_cons.mp hmem with
    | inl h => cases h  -- done ≠ memo
    | inr h => exact hInv call val (List.mem_of_mem_erase h)
  | attachWaiter req call' _ hNeed hInflight =>
    simp only [Config.add, Config.remove] at hmem
    cases List.mem_cons.mp hmem with
    | inl h => cases h  -- waiting ≠ memo
    | inr h => exact hInv call val (List.mem_of_mem_erase h)
  | firstClaim req call' _ hNeed =>
    simp only [Config.add, Config.remove] at hmem
    -- cfg' = waiting :: open :: inflight :: cfg.erase (need ...)
    cases List.mem_cons.mp hmem with
    | inl h => cases h  -- waiting ≠ memo
    | inr h => cases List.mem_cons.mp h with
      | inl h => cases h  -- open ≠ memo
      | inr h => cases List.mem_cons.mp h with
        | inl h => cases h  -- inflight ≠ memo
        | inr h => exact hInv call val (List.mem_of_mem_erase h)
  | driverSelect call' _ hDriver hOpen =>
    simp only [Config.add, Config.remove] at hmem
    cases List.mem_cons.mp hmem with
    | inl h => cases h  -- active ≠ memo
    | inr h => exact hInv call val (List.mem_of_mem_erase (List.mem_of_mem_erase h))
  | baseCase call' val' _ hActive hSem =>
    simp only [Config.add, Config.remove] at hmem
    -- cfg' = driverReady :: (memo call' val') :: cfg.erase (active call')
    cases List.mem_cons.mp hmem with
    | inl h => cases h  -- driverReady ≠ memo
    | inr h => cases List.mem_cons.mp h with
      | inl h =>
        -- h : Fact.memo call val = Fact.memo call' val'
        cases h; exact hSem
      | inr h => exact hInv call val (List.mem_of_mem_erase h)
  | expand call' _ _ _ hActive childNeeds =>
    simp only [Config.add, Config.remove] at hmem
    -- cfg' = foldl (add need) (cfg.erase (active call'))
    -- hmem : .memo call val ∈ foldl (add need) (cfg.erase (active call'))
    -- Peel back foldl (only adds .need, which is not .memo):
    have hmem_base := memo_mem_of_foldl_need hmem
    -- Peel back erase (removes .active, which is not .memo):
    exact hInv call val (List.mem_of_mem_erase hmem_base)
  | discharge req call' val' _ hMemo hWaiting =>
    simp only [Config.add, Config.remove] at hmem
    cases List.mem_cons.mp hmem with
    | inl h => cases h  -- done ≠ memo
    | inr h => exact hInv call val (List.mem_of_mem_erase h)

/-- MemoSound is preserved across multi-step reachability. -/
theorem memoSound_reaches {rules : List EvalRule} {cfg cfg' : Config}
    (hInv : MemoSound rules cfg)
    (hReach : Reaches rules cfg cfg') :
    MemoSound rules cfg' := by
  induction hReach with
  | refl => exact hInv
  | step hStep _ ih => exact ih (memoSound_step hInv hStep)

/-- Memo facts persist through every Step: if .memo call val ∈ cfg and
    Step rules cfg cfg', then .memo call val ∈ cfg'.
    This is because no Step constructor removes a .memo fact. -/
theorem memo_persists_step {rules : List EvalRule} {cfg cfg' : Config}
    {call : CallKey} {val : EvalValue}
    (hmem : Fact.memo call val ∈ cfg)
    (hStep : Step rules cfg cfg') :
    Fact.memo call val ∈ cfg' := by
  -- Every Step adds non-memo facts and removes non-memo facts.
  -- So memo membership survives.
  -- Helper: a ∈ l → a ≠ b → a ∈ l.erase b
  have memEraseNe : ∀ {a b : Fact} {l : Config}, a ∈ l → a ≠ b → a ∈ l.erase b := by
    intro a b l hm hne
    induction l with
    | nil => exact absurd hm List.not_mem_nil
    | cons hd tl ih =>
      simp [List.erase]
      by_cases hbd : hd == b
      · -- hd = b: erase removes hd, so a must be in tl
        simp [hbd]
        cases List.mem_cons.mp hm with
        | inl h => rw [h] at hne; simp [beq_iff_eq] at hbd; exact absurd hbd hne
        | inr h => exact h
      · -- hd ≠ b: erase skips hd
        simp [hbd]
        cases List.mem_cons.mp hm with
        | inl h => exact Or.inl h
        | inr h => exact Or.inr (ih h)
  cases hStep with
  | memoHit _ _ _ _ hNeed _ =>
    exact List.mem_cons_of_mem _ (memEraseNe hmem (by intro h; cases h))
  | attachWaiter _ _ _ hNeed _ =>
    exact List.mem_cons_of_mem _ (memEraseNe hmem (by intro h; cases h))
  | firstClaim _ _ _ hNeed =>
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (memEraseNe hmem (by intro h; cases h))))
  | driverSelect _ _ _ _ =>
    exact List.mem_cons_of_mem _ (memEraseNe (memEraseNe hmem (by intro h; cases h)) (by intro h; cases h))
  | baseCase _ _ _ _ _ =>
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (memEraseNe hmem (by intro h; cases h)))
  | expand _ _ _ _ _ childNeeds =>
    exact memo_mem_foldl_need (memEraseNe hmem (by intro h; cases h))
  | discharge _ _ _ _ _ _ =>
    exact List.mem_cons_of_mem _ (memEraseNe hmem (by intro h; cases h))

/-- Memo facts persist across multi-step reachability. -/
theorem memo_persists_reaches {rules : List EvalRule} {cfg cfg' : Config}
    {call : CallKey} {val : EvalValue}
    (hmem : Fact.memo call val ∈ cfg)
    (hReach : Reaches rules cfg cfg') :
    Fact.memo call val ∈ cfg' := by
  induction hReach with
  | refl => exact hmem
  | step hStep _ ih => exact ih (memo_persists_step hmem hStep)

/-- DoneBacked: every done fact in cfg has a corresponding memo fact also in cfg.
    This connects done-soundness to memo-soundness. -/
def DoneBacked (cfg : Config) : Prop :=
  ∀ req val, .done req val ∈ cfg → ∃ call, .memo call val ∈ cfg

/-- DoneBacked holds for the initial config (no done facts). -/
theorem doneBacked_initial (call : CallKey) : DoneBacked (initialConfig call) := by
  intro req val hmem; simp [initialConfig, List.mem_cons] at hmem

/-- Helper: .done survives foldl that only adds .need facts. -/
private theorem done_mem_of_foldl_need {req : ReqId} {val : EvalValue}
    {acc : Config} {needs : List (ReqId × CallKey)}
    (hmem : Fact.done req val ∈ needs.foldl (fun c ⟨rid, child⟩ => c.add (.need rid child)) acc) :
    Fact.done req val ∈ acc := by
  induction needs generalizing acc with
  | nil => exact hmem
  | cons head rest ih =>
    simp [List.foldl] at hmem; have := ih hmem
    cases List.mem_cons.mp this with
    | inl h => cases h  -- need ≠ done
    | inr h => exact h

/-- DoneBacked is preserved by every Step transition.
    Key: memoHit and discharge create (done req val) from existing memo facts,
    and memo facts persist through all Steps (via memo_persists_step). -/
theorem doneBacked_step {rules : List EvalRule} {cfg cfg' : Config}
    (hInv : DoneBacked cfg)
    (hStep : Step rules cfg cfg') :
    DoneBacked cfg' := by
  -- Strategy: for old done facts, use hInv to get memo in cfg, then
  -- memo_persists_step to get memo in cfg'. For new done facts (from
  -- memoHit/discharge), the source memo fact persists.
  have memoPersist := fun {c v} (hm : Fact.memo c v ∈ cfg) => memo_persists_step hm hStep
  intro req val hmem
  cases hStep with
  | memoHit req' call' val' _ hNeed hMemo =>
    simp only [Config.add, Config.remove] at hmem
    cases List.mem_cons.mp hmem with
    | inl h => cases h; exact ⟨call', memoPersist hMemo⟩
    | inr h =>
      obtain ⟨call, hm⟩ := hInv req val (List.mem_of_mem_erase h)
      exact ⟨call, memoPersist hm⟩
  | attachWaiter req' call' _ hNeed hInflight =>
    simp only [Config.add, Config.remove] at hmem
    cases List.mem_cons.mp hmem with
    | inl h => cases h
    | inr h =>
      obtain ⟨call, hm⟩ := hInv req val (List.mem_of_mem_erase h)
      exact ⟨call, memoPersist hm⟩
  | firstClaim req' call' _ hNeed =>
    simp only [Config.add, Config.remove] at hmem
    rcases List.mem_cons.mp hmem with h | h
    · cases h
    · rcases List.mem_cons.mp h with h | h
      · cases h
      · rcases List.mem_cons.mp h with h | h
        · cases h
        · obtain ⟨call, hm⟩ := hInv req val (List.mem_of_mem_erase h)
          exact ⟨call, memoPersist hm⟩
  | driverSelect call' _ hDriver hOpen =>
    simp only [Config.add, Config.remove] at hmem
    cases List.mem_cons.mp hmem with
    | inl h => cases h
    | inr h =>
      obtain ⟨call, hm⟩ := hInv req val (List.mem_of_mem_erase (List.mem_of_mem_erase h))
      exact ⟨call, memoPersist hm⟩
  | baseCase call' val' _ hActive hSem =>
    simp only [Config.add, Config.remove] at hmem
    rcases List.mem_cons.mp hmem with h | h
    · cases h
    · rcases List.mem_cons.mp h with h | h
      · cases h
      · obtain ⟨call, hm⟩ := hInv req val (List.mem_of_mem_erase h)
        exact ⟨call, memoPersist hm⟩
  | expand call' _ _ _ hActive childNeeds =>
    simp only [Config.add, Config.remove] at hmem
    have h := done_mem_of_foldl_need hmem
    obtain ⟨call, hm⟩ := hInv req val (List.mem_of_mem_erase h)
    exact ⟨call, memoPersist hm⟩
  | discharge req' call' val' _ hMemo hWaiting =>
    simp only [Config.add, Config.remove] at hmem
    cases List.mem_cons.mp hmem with
    | inl h => cases h; exact ⟨call', memoPersist hMemo⟩
    | inr h =>
      obtain ⟨call, hm⟩ := hInv req val (List.mem_of_mem_erase h)
      exact ⟨call, memoPersist hm⟩

/-- DoneBacked is preserved across multi-step reachability. -/
theorem doneBacked_reaches {rules : List EvalRule} {cfg cfg' : Config}
    (hInv : DoneBacked cfg)
    (hReach : Reaches rules cfg cfg') :
    DoneBacked cfg' := by
  induction hReach with
  | refl => exact hInv
  | step hStep _ ih => exact ih (doneBacked_step hInv hStep)

/-- Machine soundness — memo facts:
    Every memo fact in a reachable configuration is semantically correct. -/
theorem machine_memo_sound {rules : List EvalRule} {call : CallKey}
    {cfg : Config}
    (hReach : Reaches rules (initialConfig call) cfg)
    (callKey : CallKey) (val : EvalValue)
    (hMemo : .memo callKey val ∈ cfg) :
    EvalSem rules (.userCall callKey.head (callKey.args.map EvalValue.toNode)) val :=
  memoSound_reaches (memoSound_initial call) hReach callKey val hMemo

/-- Machine soundness — done facts:
    Every done fact in a reachable configuration is backed by a semantically
    correct memo fact. Combined with machine_memo_sound, this gives full
    answer correctness. -/
theorem machine_done_sound {rules : List EvalRule} {call : CallKey}
    {cfg : Config}
    (hReach : Reaches rules (initialConfig call) cfg)
    (req : ReqId) (val : EvalValue)
    (hDone : .done req val ∈ cfg) :
    ∃ ck : CallKey, EvalSem rules (.userCall ck.head (ck.args.map EvalValue.toNode)) val := by
  obtain ⟨ck, hMemo⟩ := doneBacked_reaches (doneBacked_initial call) hReach req val hDone
  exact ⟨ck, machine_memo_sound hReach ck val hMemo⟩

-- ═══════════════════════════════════════════════════════════════════════════
-- § Concrete fib example (validation)
-- ═══════════════════════════════════════════════════════════════════════════

/-- CallKey for fib(n). -/
def fibCall (n : Int) : CallKey := ⟨"fib", [.int n]⟩

/-- The initial configuration for fib(5). -/
def fib5_init : Config := initialConfig (fibCall 5)

-- The hand-traced execution for fib(5) would be validated in the MM2 PoC.
-- The Lean definition here is the AUTHORITY; the MM2 program must match it.

end MeTTailCore.EvalIRMachine
