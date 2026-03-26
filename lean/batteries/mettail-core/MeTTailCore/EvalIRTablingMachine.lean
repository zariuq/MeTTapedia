import MeTTailCore.EvalIRMachine

namespace MeTTailCore.EvalIRTablingMachine

open MeTTailCore.EvalIR

/-- Reuse the deterministic machine's request-id transport. -/
abbrev ReqId := MeTTailCore.EvalIRMachine.ReqId

/-- Reuse the deterministic machine's canonical call keys. -/
abbrev CallKey := MeTTailCore.EvalIRMachine.CallKey

/-- The semantic call represented by a tabling-machine key. -/
def callNode (call : CallKey) : EvalNode :=
  .userCall call.head (call.args.map EvalValue.toNode)

/-- Preserve unique answers while keeping left-to-right arrival order.

Positive example: re-adding `5` to `[3, 5]` keeps `[3, 5]`.
Negative example: this machine tracks answer sets, not multiplicity. -/
def pushUniqueAnswer (answers : List EvalValue) (value : EvalValue) : List EvalValue :=
  if value ∈ answers then answers else answers ++ [value]

/-- Every answer already present in the table has been delivered to this waiter. -/
def DeliveredAll (answers seen : List EvalValue) : Prop :=
  ∀ v, v ∈ answers → v ∈ seen

/-- Nondeterministic worklist/tabling facts.

Positive example: `.table call [7, 8] true` means the call has exactly those
ground answers and is complete.
Negative example: this does not yet model infinite answer streams. -/
inductive Fact where
  | need        : ReqId → CallKey → Fact
  | waiting     : ReqId → CallKey → List EvalValue → Fact
  | done        : ReqId → EvalValue → Fact
  | finished    : ReqId → CallKey → Fact
  | table       : CallKey → List EvalValue → Bool → Fact
  | open        : CallKey → Fact
  | active      : CallKey → Fact
  | driverReady : Fact
deriving DecidableEq, Repr

/-- A tabling-machine configuration is still a list-backed atom space. -/
abbrev Config := List Fact

def Config.remove (cfg : Config) (f : Fact) : Config := cfg.erase f
def Config.add (cfg : Config) (f : Fact) : Config := f :: cfg

/-- Emit one `done` fact for each known answer of a request. -/
def emitDoneFacts (req : ReqId) (answers : List EvalValue) (cfg : Config) : Config :=
  answers.foldl (fun c v => Fact.done req v :: c) cfg

/-- One abstract tabling step for the current finite-answer fragment. -/
inductive Step (rules : List EvalRule) : Config → Config → Prop where
  | tableHitComplete (req : ReqId) (call : CallKey) (answers : List EvalValue) (cfg : Config) :
      Fact.need req call ∈ cfg →
      Fact.table call answers true ∈ cfg →
      Step rules cfg
        (emitDoneFacts req answers (cfg.remove (Fact.need req call) |>.add (Fact.finished req call)))

  | attachConsumer (req : ReqId) (call : CallKey) (answers : List EvalValue) (cfg : Config) :
      Fact.need req call ∈ cfg →
      Fact.table call answers false ∈ cfg →
      Step rules cfg
        (emitDoneFacts req answers (cfg.remove (Fact.need req call) |>.add (Fact.waiting req call answers)))

  | firstClaim (req : ReqId) (call : CallKey) (cfg : Config) :
      Fact.need req call ∈ cfg →
      Step rules cfg
        (cfg.remove (Fact.need req call)
         |>.add (Fact.table call [] false)
         |>.add (Fact.open call)
         |>.add (Fact.waiting req call []))

  | driverSelect (call : CallKey) (cfg : Config) :
      Fact.driverReady ∈ cfg →
      Fact.open call ∈ cfg →
      Step rules cfg
        (cfg.remove Fact.driverReady |>.remove (Fact.open call) |>.add (Fact.active call))

  | newAnswer (call : CallKey) (answers : List EvalValue) (val : EvalValue) (cfg : Config) :
      Fact.active call ∈ cfg →
      Fact.table call answers false ∈ cfg →
      EvalSem rules (callNode call) val →
      Step rules cfg
        (cfg.remove (Fact.table call answers false)
         |>.add (Fact.table call (pushUniqueAnswer answers val) false))

  | dischargeAnswer
      (req : ReqId) (call : CallKey) (seen answers : List EvalValue)
      (complete : Bool) (val : EvalValue) (cfg : Config) :
      Fact.waiting req call seen ∈ cfg →
      Fact.table call answers complete ∈ cfg →
      val ∈ answers →
      val ∉ seen →
      Step rules cfg
        (cfg.remove (Fact.waiting req call seen)
         |>.add (Fact.waiting req call (pushUniqueAnswer seen val))
         |>.add (Fact.done req val))

  | completeCall (call : CallKey) (answers : List EvalValue) (cfg : Config) :
      Fact.active call ∈ cfg →
      Fact.table call answers false ∈ cfg →
      Step rules cfg
        (cfg.remove (Fact.active call)
         |>.remove (Fact.table call answers false)
         |>.add (Fact.table call answers true)
         |>.add Fact.driverReady)

  | finishWaiting (req : ReqId) (call : CallKey) (seen answers : List EvalValue) (cfg : Config) :
      Fact.waiting req call seen ∈ cfg →
      Fact.table call answers true ∈ cfg →
      DeliveredAll answers seen →
      Step rules cfg
        (cfg.remove (Fact.waiting req call seen) |>.add (Fact.finished req call))

/-- Multi-step reachability for the tabling machine. -/
inductive Reaches (rules : List EvalRule) : Config → Config → Prop where
  | refl : Reaches rules cfg cfg
  | step : Step rules cfg₁ cfg₂ → Reaches rules cfg₂ cfg₃ → Reaches rules cfg₁ cfg₃

theorem Reaches.trans
    {rules : List EvalRule} {cfg₁ cfg₂ cfg₃ : Config}
    (h₁₂ : Reaches rules cfg₁ cfg₂)
    (h₂₃ : Reaches rules cfg₂ cfg₃) :
    Reaches rules cfg₁ cfg₃ := by
  induction h₁₂ with
  | refl => exact h₂₃
  | step hStep hTail ih => exact Reaches.step hStep (ih h₂₃)

/-- Initial configuration for a root tabling query. -/
def initialConfig (call : CallKey) : Config :=
  [Fact.need 0 call, Fact.driverReady]

/-- Every answer recorded in every table is semantically valid for that call. -/
def TableSound (rules : List EvalRule) (cfg : Config) : Prop :=
  ∀ call answers complete,
    Fact.table call answers complete ∈ cfg →
    ∀ v, v ∈ answers → EvalSem rules (callNode call) v

/-- Every finished request is backed by a complete table for the same call. -/
def FinishedBacked (cfg : Config) : Prop :=
  ∀ req call, Fact.finished req call ∈ cfg → ∃ answers, Fact.table call answers true ∈ cfg

/-- Every emitted answer is backed by a table that already contains it.

Positive example: if `(done req 7)` appears, some `table call answers complete`
in the same config already contains `7`.
Negative example: this machine never treats a bare `done` fact as self-justifying. -/
def DoneBacked (cfg : Config) : Prop :=
  ∀ req val, Fact.done req val ∈ cfg →
    ∃ call answers complete, Fact.table call answers complete ∈ cfg ∧ val ∈ answers

/-- Sink-free table monotonicity for the current finite-answer tabling machine.

Positive example: a later table may gain answers or flip from open to complete,
but it never loses an already-known answer.
Negative example: this does not yet cover infinite-answer streams or table
deletion, both of which are outside the current fragment. -/
def TableAnswersGrow (cfg cfg' : Config) : Prop :=
  ∀ call answers complete,
    Fact.table call answers complete ∈ cfg →
      ∃ answers' complete',
        Fact.table call answers' complete' ∈ cfg' ∧
        DeliveredAll answers answers' ∧
        (complete = true → complete' = true)

theorem tableSound_initial (call : CallKey) :
    TableSound rules (initialConfig call) := by
  intro ck answers complete htable
  simp [initialConfig] at htable

theorem finishedBacked_initial (call : CallKey) :
    FinishedBacked (initialConfig call) := by
  intro req ck hfinished
  simp [initialConfig] at hfinished

theorem doneBacked_initial (call : CallKey) :
    DoneBacked (initialConfig call) := by
  intro req val hdone
  simp [initialConfig] at hdone

theorem deliveredAll_refl (answers : List EvalValue) :
    DeliveredAll answers answers := by
  intro v hv
  exact hv

theorem deliveredAll_pushUniqueAnswer (answers : List EvalValue) (value : EvalValue) :
    DeliveredAll answers (pushUniqueAnswer answers value) := by
  intro v hv
  unfold pushUniqueAnswer
  by_cases h : value ∈ answers
  · simpa [h] using hv
  · have : v ∈ answers ++ [value] := by
      simp [List.mem_append, hv]
    simpa [h] using this

theorem deliveredAll_trans
    {answers mid final : List EvalValue}
    (h₁ : DeliveredAll answers mid)
    (h₂ : DeliveredAll mid final) :
    DeliveredAll answers final := by
  intro v hv
  exact h₂ v (h₁ v hv)

private theorem table_mem_erase_of_ne
    {call : CallKey} {answers : List EvalValue} {complete : Bool}
    {f : Fact} {cfg : Config}
    (hmem : Fact.table call answers complete ∈ cfg)
    (hne : Fact.table call answers complete ≠ f) :
    Fact.table call answers complete ∈ cfg.erase f :=
  List.mem_erase_of_ne hne |>.mpr hmem

private theorem fact_mem_erase_of_ne
    {f g : Fact} {cfg : Config}
    (hmem : f ∈ cfg)
    (hne : f ≠ g) :
    f ∈ cfg.erase g :=
  List.mem_erase_of_ne hne |>.mpr hmem

private theorem table_mem_cons_of_mem
    {call : CallKey} {answers : List EvalValue} {complete : Bool}
    {f : Fact} {cfg : Config}
    (hmem : Fact.table call answers complete ∈ cfg) :
    Fact.table call answers complete ∈ f :: cfg :=
  List.mem_cons_of_mem _ hmem

private theorem table_mem_of_cons_of_ne
    {call : CallKey} {answers : List EvalValue} {complete : Bool}
    {f : Fact} {cfg : Config}
    (hmem : Fact.table call answers complete ∈ f :: cfg)
    (hne : Fact.table call answers complete ≠ f) :
    Fact.table call answers complete ∈ cfg := by
  cases List.mem_cons.mp hmem with
  | inl h => exact False.elim (hne h)
  | inr h => exact h

private theorem table_mem_emitDoneFacts_iff
    {call : CallKey} {answers : List EvalValue} {complete : Bool}
    {req : ReqId} {delivered : List EvalValue} {cfg : Config} :
    Fact.table call answers complete ∈ emitDoneFacts req delivered cfg ↔
      Fact.table call answers complete ∈ cfg := by
  induction delivered generalizing cfg with
  | nil =>
      simp [emitDoneFacts]
  | cons val rest ih =>
      constructor
      · intro hmem
        have hmem' :
            Fact.table call answers complete ∈
              emitDoneFacts req rest (Fact.done req val :: cfg) := by
          simpa [emitDoneFacts, List.foldl] using hmem
        have hbase : Fact.table call answers complete ∈ Fact.done req val :: cfg :=
          ih.mp hmem'
        exact table_mem_of_cons_of_ne hbase (by intro h; cases h)
      · intro hmem
        have hcons : Fact.table call answers complete ∈ Fact.done req val :: cfg :=
          table_mem_cons_of_mem hmem
        have hrest :
            Fact.table call answers complete ∈
              emitDoneFacts req rest (Fact.done req val :: cfg) :=
          ih.mpr hcons
        simpa [emitDoneFacts, List.foldl] using hrest

private theorem finished_mem_emitDoneFacts_iff
    {req0 : ReqId} {call0 : CallKey}
    {req : ReqId} {delivered : List EvalValue} {cfg : Config} :
    Fact.finished req0 call0 ∈ emitDoneFacts req delivered cfg ↔
      Fact.finished req0 call0 ∈ cfg := by
  induction delivered generalizing cfg with
  | nil =>
      simp [emitDoneFacts]
  | cons val rest ih =>
      constructor
      · intro hmem
        have hmem' :
            Fact.finished req0 call0 ∈
              emitDoneFacts req rest (Fact.done req val :: cfg) := by
          simpa [emitDoneFacts, List.foldl] using hmem
        have hbase : Fact.finished req0 call0 ∈ Fact.done req val :: cfg :=
          ih.mp hmem'
        cases List.mem_cons.mp hbase with
        | inl h => cases h
        | inr h => exact h
      · intro hmem
        have hcons : Fact.finished req0 call0 ∈ Fact.done req val :: cfg :=
          List.mem_cons_of_mem _ hmem
        have hrest :
            Fact.finished req0 call0 ∈
              emitDoneFacts req rest (Fact.done req val :: cfg) :=
          ih.mpr hcons
        simpa [emitDoneFacts, List.foldl] using hrest

private theorem waiting_mem_emitDoneFacts_iff
    {req0 : ReqId} {call0 : CallKey} {seen0 : List EvalValue}
    {req : ReqId} {delivered : List EvalValue} {cfg : Config} :
    Fact.waiting req0 call0 seen0 ∈ emitDoneFacts req delivered cfg ↔
      Fact.waiting req0 call0 seen0 ∈ cfg := by
  induction delivered generalizing cfg with
  | nil =>
      simp [emitDoneFacts]
  | cons val rest ih =>
      constructor
      · intro hmem
        have hmem' :
            Fact.waiting req0 call0 seen0 ∈
              emitDoneFacts req rest (Fact.done req val :: cfg) := by
          simpa [emitDoneFacts, List.foldl] using hmem
        have hbase : Fact.waiting req0 call0 seen0 ∈ Fact.done req val :: cfg :=
          ih.mp hmem'
        cases List.mem_cons.mp hbase with
        | inl h => cases h
        | inr h => exact h
      · intro hmem
        have hcons : Fact.waiting req0 call0 seen0 ∈ Fact.done req val :: cfg :=
          List.mem_cons_of_mem _ hmem
        have hrest :
            Fact.waiting req0 call0 seen0 ∈
              emitDoneFacts req rest (Fact.done req val :: cfg) :=
          ih.mpr hcons
        simpa [emitDoneFacts, List.foldl] using hrest

private theorem done_mem_emitDoneFacts_iff
    {req0 : ReqId} {val0 : EvalValue}
    {req : ReqId} {delivered : List EvalValue} {cfg : Config} :
    Fact.done req0 val0 ∈ emitDoneFacts req delivered cfg ↔
      (req0 = req ∧ val0 ∈ delivered) ∨ Fact.done req0 val0 ∈ cfg := by
  induction delivered generalizing cfg with
  | nil =>
      simp [emitDoneFacts]
  | cons val rest ih =>
      constructor
      · intro hmem
        have hmem' :
            Fact.done req0 val0 ∈
              emitDoneFacts req rest (Fact.done req val :: cfg) := by
          simpa [emitDoneFacts, List.foldl] using hmem
        rcases ih.mp hmem' with hnew | hold
        · exact Or.inl ⟨hnew.1, List.mem_cons_of_mem _ hnew.2⟩
        · cases List.mem_cons.mp hold with
          | inl h =>
              cases h
              exact Or.inl ⟨rfl, List.mem_cons_self⟩
          | inr h =>
              exact Or.inr h
      · intro hmem
        rcases hmem with hnew | hold
        · rcases hnew with ⟨hreq, hmem⟩
          have hrest :
              Fact.done req0 val0 ∈
                emitDoneFacts req rest (Fact.done req val :: cfg) := by
            cases hreq
            cases List.mem_cons.mp hmem with
            | inl h =>
                cases h
                have hseed : Fact.done req0 val0 ∈ Fact.done req0 val0 :: cfg :=
                  List.mem_cons_self
                exact ih.mpr (Or.inr hseed)
            | inr h =>
                exact ih.mpr (Or.inl ⟨rfl, h⟩)
          simpa [emitDoneFacts, List.foldl] using hrest
        · have hseed : Fact.done req0 val0 ∈ Fact.done req val :: cfg :=
            List.mem_cons_of_mem _ hold
          have hrest :
              Fact.done req0 val0 ∈
                emitDoneFacts req rest (Fact.done req val :: cfg) :=
            ih.mpr (Or.inr hseed)
          simpa [emitDoneFacts, List.foldl] using hrest

theorem mem_pushUniqueAnswer {answers : List EvalValue} {value v : EvalValue} :
    v ∈ pushUniqueAnswer answers value ↔ v = value ∨ v ∈ answers := by
  unfold pushUniqueAnswer
  by_cases h : value ∈ answers
  · constructor
    · intro hv
      exact Or.inr (by simpa [h] using hv)
    · intro hv
      cases hv with
      | inl hEq =>
          cases hEq
          simp [h]
      | inr hMem =>
          simpa [h] using hMem
  · constructor
    · intro hv
      have hv' : v ∈ answers ++ [value] := by
        simpa [h] using hv
      simp [List.mem_append] at hv'
      cases hv' with
      | inl hMem => exact Or.inr hMem
      | inr hMem =>
          simp at hMem
          exact Or.inl hMem
    · intro hv
      have hv' : v ∈ answers ++ [value] := by
        cases hv with
        | inl hEq =>
            cases hEq
            simp
        | inr hMem =>
            simp [List.mem_append, hMem]
      simpa [h] using hv'

theorem attachConsumer_waiting_mem
    (req : ReqId) (call : CallKey) (answers : List EvalValue) (cfg : Config) :
    Fact.waiting req call answers ∈
      emitDoneFacts req answers (cfg.remove (Fact.need req call) |>.add (Fact.waiting req call answers)) := by
  apply waiting_mem_emitDoneFacts_iff.mpr
  exact List.mem_cons_self

theorem attachConsumer_done_mem
    (req : ReqId) (call : CallKey) (answers : List EvalValue) (cfg : Config)
    {val : EvalValue} (hVal : val ∈ answers) :
    Fact.done req val ∈
      emitDoneFacts req answers (cfg.remove (Fact.need req call) |>.add (Fact.waiting req call answers)) := by
  exact (done_mem_emitDoneFacts_iff).2 (Or.inl ⟨rfl, hVal⟩)

theorem tableHitComplete_finished_mem
    (req : ReqId) (call : CallKey) (answers : List EvalValue) (cfg : Config) :
    Fact.finished req call ∈
      emitDoneFacts req answers (cfg.remove (Fact.need req call) |>.add (Fact.finished req call)) := by
  apply finished_mem_emitDoneFacts_iff.mpr
  exact List.mem_cons_self

theorem tableHitComplete_done_mem
    (req : ReqId) (call : CallKey) (answers : List EvalValue) (cfg : Config)
    {val : EvalValue} (hVal : val ∈ answers) :
    Fact.done req val ∈
      emitDoneFacts req answers (cfg.remove (Fact.need req call) |>.add (Fact.finished req call)) := by
  exact (done_mem_emitDoneFacts_iff).2 (Or.inl ⟨rfl, hVal⟩)

theorem dischargeAnswer_waiting_mem
    (req : ReqId) (call : CallKey) (seen : List EvalValue) (val : EvalValue) (cfg : Config) :
    Fact.waiting req call (pushUniqueAnswer seen val) ∈
      (cfg.remove (Fact.waiting req call seen)
        |>.add (Fact.waiting req call (pushUniqueAnswer seen val))
        |>.add (Fact.done req val)) := by
  simp [Config.add]

theorem dischargeAnswer_done_mem
    (req : ReqId) (call : CallKey) (seen : List EvalValue) (val : EvalValue) (cfg : Config) :
    Fact.done req val ∈
      (cfg.remove (Fact.waiting req call seen)
        |>.add (Fact.waiting req call (pushUniqueAnswer seen val))
        |>.add (Fact.done req val)) := by
  simp [Config.add]

theorem newAnswer_table_mem
    (call : CallKey) (answers : List EvalValue) (val : EvalValue) (cfg : Config) :
    Fact.table call (pushUniqueAnswer answers val) false ∈
      (cfg.remove (Fact.table call answers false)
        |>.add (Fact.table call (pushUniqueAnswer answers val) false)) := by
  simp [Config.add]

theorem completeCall_complete_table_mem
    (call : CallKey) (answers : List EvalValue) (cfg : Config) :
    Fact.table call answers true ∈
      (cfg.remove (Fact.active call)
        |>.remove (Fact.table call answers false)
        |>.add (Fact.table call answers true)
        |>.add Fact.driverReady) := by
  simp [Config.add]

theorem completeCall_driverReady_mem
    (call : CallKey) (answers : List EvalValue) (cfg : Config) :
    Fact.driverReady ∈
      (cfg.remove (Fact.active call)
        |>.remove (Fact.table call answers false)
        |>.add (Fact.table call answers true)
        |>.add Fact.driverReady) := by
  simp [Config.add]

theorem finishWaiting_finished_mem
    (req : ReqId) (call : CallKey) (seen _answers : List EvalValue) (cfg : Config) :
    Fact.finished req call ∈
      (cfg.remove (Fact.waiting req call seen) |>.add (Fact.finished req call)) := by
  simp [Config.add]

theorem attachConsumer_step_waits_and_replays
    {rules : List EvalRule}
    (req : ReqId) (call : CallKey) (answers : List EvalValue) (cfg : Config)
    (hNeed : Fact.need req call ∈ cfg)
    (hTable : Fact.table call answers false ∈ cfg) :
    ∃ cfg', Step rules cfg cfg' ∧
      Fact.waiting req call answers ∈ cfg' ∧
      ∀ v, v ∈ answers → Fact.done req v ∈ cfg' := by
  refine ⟨_, Step.attachConsumer req call answers cfg hNeed hTable, ?_, ?_⟩
  · exact attachConsumer_waiting_mem req call answers cfg
  · intro v hv
    exact attachConsumer_done_mem req call answers cfg hv

theorem tableHitComplete_step_finishes_and_replays
    {rules : List EvalRule}
    (req : ReqId) (call : CallKey) (answers : List EvalValue) (cfg : Config)
    (hNeed : Fact.need req call ∈ cfg)
    (hTable : Fact.table call answers true ∈ cfg) :
    ∃ cfg', Step rules cfg cfg' ∧
      Fact.finished req call ∈ cfg' ∧
      ∀ v, v ∈ answers → Fact.done req v ∈ cfg' := by
  refine ⟨_, Step.tableHitComplete req call answers cfg hNeed hTable, ?_, ?_⟩
  · exact tableHitComplete_finished_mem req call answers cfg
  · intro v hv
    exact tableHitComplete_done_mem req call answers cfg hv

theorem newAnswer_step_adds_answer
    {rules : List EvalRule}
    (call : CallKey) (answers : List EvalValue) (val : EvalValue) (cfg : Config)
    (hActive : Fact.active call ∈ cfg)
    (hTable : Fact.table call answers false ∈ cfg)
    (hSem : EvalSem rules (callNode call) val) :
    ∃ cfg', Step rules cfg cfg' ∧
      Fact.table call (pushUniqueAnswer answers val) false ∈ cfg' := by
  refine ⟨_, Step.newAnswer call answers val cfg hActive hTable hSem, ?_⟩
  exact newAnswer_table_mem call answers val cfg

theorem dischargeAnswer_step_updates_waiter
    {rules : List EvalRule}
    (req : ReqId) (call : CallKey) (seen answers : List EvalValue)
    (complete : Bool) (val : EvalValue) (cfg : Config)
    (hWaiting : Fact.waiting req call seen ∈ cfg)
    (hTable : Fact.table call answers complete ∈ cfg)
    (hVal : val ∈ answers)
    (hFresh : val ∉ seen) :
    ∃ cfg', Step rules cfg cfg' ∧
      Fact.waiting req call (pushUniqueAnswer seen val) ∈ cfg' ∧
      Fact.done req val ∈ cfg' := by
  refine ⟨_, Step.dischargeAnswer req call seen answers complete val cfg hWaiting hTable hVal hFresh, ?_, ?_⟩
  · exact dischargeAnswer_waiting_mem req call seen val cfg
  · exact dischargeAnswer_done_mem req call seen val cfg

theorem completeCall_step_marks_complete
    {rules : List EvalRule}
    (call : CallKey) (answers : List EvalValue) (cfg : Config)
    (hActive : Fact.active call ∈ cfg)
    (hTable : Fact.table call answers false ∈ cfg) :
    ∃ cfg', Step rules cfg cfg' ∧
      Fact.table call answers true ∈ cfg' ∧
      Fact.driverReady ∈ cfg' := by
  refine ⟨_, Step.completeCall call answers cfg hActive hTable, ?_, ?_⟩
  · exact completeCall_complete_table_mem call answers cfg
  · exact completeCall_driverReady_mem call answers cfg

/-- An abstract finite sealing plan for quiescent active tables.

Positive example: a mutually recursive sink component can be represented as a
list of `(call, answers)` pairs that are all ready to be sealed.
Negative example: this is not yet a graph-theoretic SCC certificate by itself;
it packages the active tables once that eligibility has already been decided. -/
abbrev SealPlan := List (CallKey × List EvalValue)

/-- The same call should not appear twice in one sealing plan. -/
def PlanDistinct (plan : SealPlan) : Prop :=
  (plan.map Prod.fst).Nodup

/-- Every plan entry is still active and has the listed open table. -/
def PlanReady (cfg : Config) (plan : SealPlan) : Prop :=
  ∀ ⦃call answers⦄, (call, answers) ∈ plan →
    Fact.active call ∈ cfg ∧ Fact.table call answers false ∈ cfg

/-- Every plan entry has been sealed to a complete table. -/
def PlanSealed (cfg : Config) (plan : SealPlan) : Prop :=
  ∀ ⦃call answers⦄, (call, answers) ∈ plan →
    Fact.table call answers true ∈ cfg

/-- A finite cyclic component that is ready to be sealed.

Positive example: a quiescent sink component can be packaged as a distinct plan
whose entries are still active with matching open tables.
Negative example: this is still not a graph-theoretic SCC witness; it is the
finite readiness layer we can prove against today. -/
def FiniteCyclicEligible (cfg : Config) (plan : SealPlan) : Prop :=
  PlanDistinct plan ∧ PlanReady cfg plan

/-- Every currently active call is covered by the candidate sealing plan.

Positive example: a quiescent sink component plan names every active table the
driver could still complete.
Negative example: a plan that omits some active call is not yet closed enough
to claim SCC-style quiescent completion. -/
def PlanCoversActive (cfg : Config) (plan : SealPlan) : Prop :=
  ∀ ⦃call⦄, Fact.active call ∈ cfg → call ∈ plan.map Prod.fst

/-- A finite cyclic plan that is ready *and* covers the current active component.

Positive example: a closed quiescent sink component whose active tables are all
named by the sealing plan.
Negative example: this is still not full graph-theoretic SLG eligibility; it is
the stronger finite closed-component layer we can prove against today. -/
def ClosedFiniteCyclicEligible (cfg : Config) (plan : SealPlan) : Prop :=
  FiniteCyclicEligible cfg plan ∧ PlanCoversActive cfg plan

private theorem fact_mem_completeCall_cfg_of_ne
    {f : Fact} {call : CallKey} {answers : List EvalValue} {cfg : Config}
    (hmem : f ∈ cfg)
    (hneActive : f ≠ Fact.active call)
    (hneTable : f ≠ Fact.table call answers false) :
    f ∈
      (cfg.remove (Fact.active call)
        |>.remove (Fact.table call answers false)
        |>.add (Fact.table call answers true)
        |>.add Fact.driverReady) := by
  have h1 : f ∈ cfg.remove (Fact.active call) :=
    fact_mem_erase_of_ne hmem hneActive
  have h2 :
      f ∈ (cfg.remove (Fact.active call)).remove (Fact.table call answers false) :=
    fact_mem_erase_of_ne h1 hneTable
  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h2)

private theorem active_mem_completeCall_cfg_of_ne
    {call other : CallKey} {answers : List EvalValue} {cfg : Config}
    (hmem : Fact.active call ∈ cfg)
    (hne : call ≠ other) :
    Fact.active call ∈
      (cfg.remove (Fact.active other)
        |>.remove (Fact.table other answers false)
        |>.add (Fact.table other answers true)
        |>.add Fact.driverReady) := by
  apply fact_mem_completeCall_cfg_of_ne hmem
  · intro hEq
    cases hEq
    exact hne rfl
  · intro hEq
    cases hEq

private theorem open_table_mem_completeCall_cfg_of_ne
    {call other : CallKey} {answers otherAnswers : List EvalValue} {cfg : Config}
    (hmem : Fact.table call answers false ∈ cfg)
    (hne : call ≠ other) :
    Fact.table call answers false ∈
      (cfg.remove (Fact.active other)
        |>.remove (Fact.table other otherAnswers false)
        |>.add (Fact.table other otherAnswers true)
        |>.add Fact.driverReady) := by
  apply fact_mem_completeCall_cfg_of_ne hmem
  · intro hEq
    cases hEq
  · intro hEq
    cases hEq
    exact hne rfl

private theorem complete_table_mem_completeCall_cfg
    {call other : CallKey} {vals otherVals : List EvalValue} {cfg : Config}
    (hmem : Fact.table call vals true ∈ cfg) :
    Fact.table call vals true ∈
      (cfg.remove (Fact.active other)
        |>.remove (Fact.table other otherVals false)
        |>.add (Fact.table other otherVals true)
        |>.add Fact.driverReady) := by
  apply fact_mem_completeCall_cfg_of_ne hmem
  · intro hEq
    cases hEq
  · intro hEq
    cases hEq

/-- A finite quiescent component can be sealed one active table at a time.

Positive example: if a reachable sink component already exposes the answers for
each active table, this theorem yields a reachable configuration where each of
those tables is complete.
Negative example: this does not yet prove that a component is *eligible* to be
sealed; it only formalizes what happens once such a finite plan is given. -/
theorem sealPlan_reaches
    {rules : List EvalRule} :
    ∀ {cfg : Config} {plan : SealPlan},
      PlanDistinct plan →
      PlanReady cfg plan →
      ∃ cfg',
        Reaches rules cfg cfg' ∧
        PlanSealed cfg' plan ∧
        (∀ call answers,
          Fact.table call answers true ∈ cfg →
            Fact.table call answers true ∈ cfg') := by
  intro cfg plan hDistinct hReady
  induction plan generalizing cfg with
  | nil =>
      refine ⟨cfg, Reaches.refl, ?_, ?_⟩
      · intro call answers hMem
        cases hMem
      · intro call answers hMem
        exact hMem
  | cons head tail ih =>
      rcases head with ⟨call, answers⟩
      have hDistinctMap : (List.map Prod.fst ((call, answers) :: tail)).Nodup := by
        simpa [PlanDistinct] using hDistinct
      rcases List.nodup_cons.mp hDistinctMap with ⟨hNotInTail, hTailDistinctMap⟩
      have hTailDistinct : PlanDistinct tail := by
        simpa [PlanDistinct] using hTailDistinctMap
      have hHeadReady : Fact.active call ∈ cfg ∧ Fact.table call answers false ∈ cfg :=
        hReady (by simp)
      rcases hHeadReady with ⟨hActive, hTable⟩
      let cfg₁ : Config :=
        (cfg.remove (Fact.active call)
          |>.remove (Fact.table call answers false)
          |>.add (Fact.table call answers true)
          |>.add Fact.driverReady)
      have hStep : Step rules cfg cfg₁ :=
        Step.completeCall call answers cfg hActive hTable
      have hComplete : Fact.table call answers true ∈ cfg₁ :=
        completeCall_complete_table_mem call answers cfg
      have hTailReady : PlanReady cfg₁ tail := by
        intro call' answers' hMem
        have hOrig : (call', answers') ∈ (call, answers) :: tail :=
          List.mem_cons_of_mem _ hMem
        have hOrigReady : Fact.active call' ∈ cfg ∧ Fact.table call' answers' false ∈ cfg :=
          hReady hOrig
        have hCallMem : call' ∈ tail.map Prod.fst := by
          exact List.mem_map.mpr ⟨(call', answers'), hMem, rfl⟩
        have hNe : call' ≠ call := by
          intro hEq
          apply hNotInTail
          simpa [hEq] using hCallMem
        exact ⟨
          active_mem_completeCall_cfg_of_ne hOrigReady.1 hNe,
          open_table_mem_completeCall_cfg_of_ne hOrigReady.2 hNe
        ⟩
      rcases ih hTailDistinct hTailReady with
        ⟨cfg₂, hTailReach, hTailSealed, hPreserve⟩
      have hHeadSealed : Fact.table call answers true ∈ cfg₂ :=
        hPreserve call answers hComplete
      refine ⟨cfg₂, Reaches.step hStep hTailReach, ?_, ?_⟩
      · intro call' answers' hMem
        cases List.mem_cons.mp hMem with
        | inl hEq =>
            cases hEq
            exact hHeadSealed
        | inr hTail =>
            exact hTailSealed hTail
      · intro call' answers' hMem
        exact hPreserve call' answers' (complete_table_mem_completeCall_cfg hMem)

theorem sealPlan_of_reaches
    {rules : List EvalRule} {root : CallKey} {cfg : Config} {plan : SealPlan}
    (hReach : Reaches rules (initialConfig root) cfg)
    (hDistinct : PlanDistinct plan)
    (hReady : PlanReady cfg plan) :
    ∃ cfg',
      Reaches rules (initialConfig root) cfg' ∧
      PlanSealed cfg' plan := by
  rcases sealPlan_reaches (rules := rules) (cfg := cfg) (plan := plan) hDistinct hReady with
    ⟨cfg', hLocal, hSealed, _hPreserve⟩
  exact ⟨cfg', Reaches.trans hReach hLocal, hSealed⟩

theorem finishWaiting_step_finishes
    {rules : List EvalRule}
    (req : ReqId) (call : CallKey) (seen answers : List EvalValue) (cfg : Config)
    (hWaiting : Fact.waiting req call seen ∈ cfg)
    (hTable : Fact.table call answers true ∈ cfg)
    (hDelivered : DeliveredAll answers seen) :
    ∃ cfg', Step rules cfg cfg' ∧ Fact.finished req call ∈ cfg' := by
  refine ⟨_, Step.finishWaiting req call seen answers cfg hWaiting hTable hDelivered, ?_⟩
  exact finishWaiting_finished_mem req call seen answers cfg

theorem waiting_progress_discharge_of_reaches
    {rules : List EvalRule} {root : CallKey} {cfg : Config}
    {req : ReqId} {call : CallKey} {seen answers : List EvalValue}
    {complete : Bool} {val : EvalValue}
    (_hReach : Reaches rules (initialConfig root) cfg)
    (hWaiting : Fact.waiting req call seen ∈ cfg)
    (hTable : Fact.table call answers complete ∈ cfg)
    (hVal : val ∈ answers)
    (hFresh : val ∉ seen) :
    ∃ cfg',
      Reaches rules cfg cfg' ∧
      Fact.waiting req call (pushUniqueAnswer seen val) ∈ cfg' ∧
      Fact.done req val ∈ cfg' := by
  rcases dischargeAnswer_step_updates_waiter
      (rules := rules) req call seen answers complete val cfg hWaiting hTable hVal hFresh with
    ⟨cfg', hStep, hWaiting', hDone⟩
  exact ⟨cfg', Reaches.step hStep Reaches.refl, hWaiting', hDone⟩

theorem waiting_progress_finish_of_reaches
    {rules : List EvalRule} {root : CallKey} {cfg : Config}
    {req : ReqId} {call : CallKey} {seen answers : List EvalValue}
    (_hReach : Reaches rules (initialConfig root) cfg)
    (hWaiting : Fact.waiting req call seen ∈ cfg)
    (hTable : Fact.table call answers true ∈ cfg)
    (hDelivered : DeliveredAll answers seen) :
    ∃ cfg',
      Reaches rules cfg cfg' ∧
      Fact.finished req call ∈ cfg' := by
  rcases finishWaiting_step_finishes
      (rules := rules) req call seen answers cfg hWaiting hTable hDelivered with
    ⟨cfg', hStep, hFinished⟩
  exact ⟨cfg', Reaches.step hStep Reaches.refl, hFinished⟩

theorem tableSound_step {rules : List EvalRule} {cfg cfg' : Config}
    (hInv : TableSound rules cfg)
    (hStep : Step rules cfg cfg') :
    TableSound rules cfg' := by
  intro call answers complete htable v hv
  cases hStep with
  | tableHitComplete req call' answers' cfg hNeed hTable =>
      have hbase :
          Fact.table call answers complete ∈
            (cfg.remove (Fact.need req call') |>.add (Fact.finished req call')) :=
        (table_mem_emitDoneFacts_iff.mp htable)
      have htrim :
          Fact.table call answers complete ∈ cfg.remove (Fact.need req call') :=
        table_mem_of_cons_of_ne hbase (by intro h; cases h)
      exact hInv call answers complete (List.mem_of_mem_erase htrim) v hv
  | attachConsumer req call' answers' cfg hNeed hTable =>
      have hbase :
          Fact.table call answers complete ∈
            (cfg.remove (Fact.need req call') |>.add (Fact.waiting req call' answers')) :=
        (table_mem_emitDoneFacts_iff.mp htable)
      have htrim :
          Fact.table call answers complete ∈ cfg.remove (Fact.need req call') :=
        table_mem_of_cons_of_ne hbase (by intro h; cases h)
      exact hInv call answers complete (List.mem_of_mem_erase htrim) v hv
  | firstClaim req call' cfg hNeed =>
      have h1 :
          Fact.table call answers complete ∈
            Fact.open call' :: Fact.table call' [] false :: cfg.remove (Fact.need req call') :=
        table_mem_of_cons_of_ne htable (by intro h; cases h)
      have h2 :
          Fact.table call answers complete ∈
            Fact.table call' [] false :: cfg.remove (Fact.need req call') :=
        table_mem_of_cons_of_ne h1 (by intro h; cases h)
      cases List.mem_cons.mp h2 with
      | inl h =>
          cases h
          simp at hv
      | inr h =>
          exact hInv call answers complete (List.mem_of_mem_erase h) v hv
  | driverSelect call' cfg hDriver hOpen =>
      have h1 :
          Fact.table call answers complete ∈
            (cfg.remove Fact.driverReady).remove (Fact.open call') :=
        table_mem_of_cons_of_ne htable (by intro h; cases h)
      exact hInv call answers complete (List.mem_of_mem_erase (List.mem_of_mem_erase h1)) v hv
  | newAnswer call' answers' val cfg hActive hTable hSem =>
      cases List.mem_cons.mp htable with
      | inl h =>
          cases h
          rw [mem_pushUniqueAnswer] at hv
          cases hv with
          | inl hvEq =>
              cases hvEq
              exact hSem
          | inr hvMem =>
              exact hInv _ _ _ hTable v hvMem
      | inr h =>
          exact hInv call answers complete (List.mem_of_mem_erase h) v hv
  | dischargeAnswer req call' seen answers' complete' val cfg hWaiting hTable hIn hNotSeen =>
      have h1 :
          Fact.table call answers complete ∈
            Fact.waiting req call' (pushUniqueAnswer seen val) :: cfg.remove (Fact.waiting req call' seen) :=
        table_mem_of_cons_of_ne htable (by intro h; cases h)
      have h2 :
          Fact.table call answers complete ∈ cfg.remove (Fact.waiting req call' seen) :=
        table_mem_of_cons_of_ne h1 (by intro h; cases h)
      exact hInv call answers complete (List.mem_of_mem_erase h2) v hv
  | completeCall call' answers' cfg hActive hTable =>
      have h1 :
          Fact.table call answers complete ∈
            Fact.table call' answers' true ::
              (cfg.remove (Fact.active call')).remove (Fact.table call' answers' false) :=
        table_mem_of_cons_of_ne htable (by intro h; cases h)
      cases List.mem_cons.mp h1 with
      | inl h =>
          cases h
          exact hInv _ _ _ hTable v hv
      | inr h =>
          exact hInv call answers complete (List.mem_of_mem_erase (List.mem_of_mem_erase h)) v hv
  | finishWaiting req call' seen answers' cfg hWaiting hTable hDelivered =>
      have h1 :
          Fact.table call answers complete ∈ cfg.remove (Fact.waiting req call' seen) :=
        table_mem_of_cons_of_ne htable (by intro h; cases h)
      exact hInv call answers complete (List.mem_of_mem_erase h1) v hv

theorem tableAnswersGrow_step {rules : List EvalRule} {cfg cfg' : Config}
    (hStep : Step rules cfg cfg') :
    TableAnswersGrow cfg cfg' := by
  intro call answers complete hSrc
  cases hStep with
  | tableHitComplete req call' answers' cfg hNeed hTable =>
      have hTrim : Fact.table call answers complete ∈ cfg.remove (Fact.need req call') :=
        table_mem_erase_of_ne hSrc (by intro hEq; cases hEq)
      have hBase :
          Fact.table call answers complete ∈
            (cfg.remove (Fact.need req call') |>.add (Fact.finished req call')) :=
        List.mem_cons_of_mem _ hTrim
      exact ⟨answers, complete, table_mem_emitDoneFacts_iff.mpr hBase,
        deliveredAll_refl answers, by intro hEq; simp [hEq]⟩
  | attachConsumer req call' answers' cfg hNeed hTable =>
      have hTrim : Fact.table call answers complete ∈ cfg.remove (Fact.need req call') :=
        table_mem_erase_of_ne hSrc (by intro hEq; cases hEq)
      have hBase :
          Fact.table call answers complete ∈
            (cfg.remove (Fact.need req call') |>.add (Fact.waiting req call' answers')) :=
        List.mem_cons_of_mem _ hTrim
      exact ⟨answers, complete, table_mem_emitDoneFacts_iff.mpr hBase,
        deliveredAll_refl answers, by intro hEq; simp [hEq]⟩
  | firstClaim req call' cfg hNeed =>
      have hTrim : Fact.table call answers complete ∈ cfg.remove (Fact.need req call') :=
        table_mem_erase_of_ne hSrc (by intro hEq; cases hEq)
      exact ⟨answers, complete,
        List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hTrim)),
        deliveredAll_refl answers, by intro hEq; simp [hEq]⟩
  | driverSelect call' cfg hDriver hOpen =>
      have hTrim₁ : Fact.table call answers complete ∈ cfg.remove Fact.driverReady :=
        table_mem_erase_of_ne hSrc (by intro hEq; cases hEq)
      have hTrim₂ :
          Fact.table call answers complete ∈
            (cfg.remove Fact.driverReady).remove (Fact.open call') :=
        table_mem_erase_of_ne hTrim₁ (by intro hEq; cases hEq)
      exact ⟨answers, complete, List.mem_cons_of_mem _ hTrim₂,
        deliveredAll_refl answers, by intro hEq; simp [hEq]⟩
  | newAnswer call' answers' val cfg hActive hTable hSem =>
      by_cases hSame : call = call' ∧ complete = false ∧ answers = answers'
      · rcases hSame with ⟨rfl, rfl, rfl⟩
        exact ⟨pushUniqueAnswer answers val, false, List.mem_cons_self,
          deliveredAll_pushUniqueAnswer answers val,
          by intro hEq; cases hEq⟩
      · have hNeTable : Fact.table call answers complete ≠ Fact.table call' answers' false := by
          intro hEq
          cases hEq
          exact hSame ⟨rfl, rfl, rfl⟩
        have hTrim : Fact.table call answers complete ∈ cfg.remove (Fact.table call' answers' false) :=
          table_mem_erase_of_ne hSrc hNeTable
        exact ⟨answers, complete, List.mem_cons_of_mem _ hTrim,
          deliveredAll_refl answers, by intro hEq; simp [hEq]⟩
  | dischargeAnswer req call' seen answers' complete' val cfg hWaiting hTable hIn hNotSeen =>
      have hTrim : Fact.table call answers complete ∈ cfg.remove (Fact.waiting req call' seen) :=
        table_mem_erase_of_ne hSrc (by intro hEq; cases hEq)
      exact ⟨answers, complete,
        List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hTrim),
        deliveredAll_refl answers, by intro hEq; simp [hEq]⟩
  | completeCall call' answers' cfg hActive hTable =>
      by_cases hSame : call = call' ∧ complete = false ∧ answers = answers'
      · rcases hSame with ⟨rfl, rfl, rfl⟩
        exact ⟨answers, true, List.mem_cons_of_mem _ List.mem_cons_self,
          deliveredAll_refl answers, by intro hEq; cases hEq⟩
      · have hTrim₁ : Fact.table call answers complete ∈ cfg.remove (Fact.active call') :=
          table_mem_erase_of_ne hSrc (by intro hEq; cases hEq)
        have hNeTable : Fact.table call answers complete ≠ Fact.table call' answers' false := by
          intro hEq
          cases hEq
          exact hSame ⟨rfl, rfl, rfl⟩
        have hTrim₂ :
            Fact.table call answers complete ∈
              (cfg.remove (Fact.active call')).remove (Fact.table call' answers' false) :=
          table_mem_erase_of_ne hTrim₁ hNeTable
        exact ⟨answers, complete,
          List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hTrim₂),
          deliveredAll_refl answers, by intro hEq; simp [hEq]⟩
  | finishWaiting req call' seen answers' cfg hWaiting hTable hDelivered =>
      have hTrim : Fact.table call answers complete ∈ cfg.remove (Fact.waiting req call' seen) :=
        table_mem_erase_of_ne hSrc (by intro hEq; cases hEq)
      exact ⟨answers, complete, List.mem_cons_of_mem _ hTrim,
        deliveredAll_refl answers, by intro hEq; simp [hEq]⟩

theorem tableAnswersGrow_reaches {rules : List EvalRule} {cfg cfg' : Config}
    (hReach : Reaches rules cfg cfg') :
    TableAnswersGrow cfg cfg' := by
  induction hReach with
  | refl =>
      intro call answers complete hSrc
      exact ⟨answers, complete, hSrc, deliveredAll_refl answers, by intro hEq; simp [hEq]⟩
  | step hStep hTail ih =>
      intro call answers complete hSrc
      obtain ⟨answers₁, complete₁, hMid, hGrow₁, hKeep₁⟩ :=
        tableAnswersGrow_step hStep call answers complete hSrc
      obtain ⟨answers₂, complete₂, hDst, hGrow₂, hKeep₂⟩ :=
        ih call answers₁ complete₁ hMid
      exact ⟨answers₂, complete₂, hDst,
        deliveredAll_trans hGrow₁ hGrow₂,
        fun hComplete => hKeep₂ (hKeep₁ hComplete)⟩

theorem tableSound_reaches {rules : List EvalRule} {cfg cfg' : Config}
    (hInv : TableSound rules cfg)
    (hReach : Reaches rules cfg cfg') :
    TableSound rules cfg' := by
  induction hReach with
  | refl => exact hInv
  | step hStep _ ih => exact ih (tableSound_step hInv hStep)

theorem doneBacked_step {cfg cfg' : Config}
    (hInv : DoneBacked cfg)
    (hStep : Step rules cfg cfg') :
    DoneBacked cfg' := by
  intro req val hdone
  cases hStep with
  | tableHitComplete req' call' answers' cfg hNeed hTable =>
      rcases done_mem_emitDoneFacts_iff.mp hdone with hnew | hold
      · rcases hnew with ⟨hreq, hval⟩
        cases hreq
        have htrim : Fact.table call' answers' true ∈ cfg.remove (Fact.need req call') :=
          table_mem_erase_of_ne hTable (by intro hEq; cases hEq)
        have hcfg' : Fact.table call' answers' true ∈
            emitDoneFacts req answers'
              (cfg.remove (Fact.need req call') |>.add (Fact.finished req call')) :=
          table_mem_emitDoneFacts_iff.mpr (List.mem_cons_of_mem _ htrim)
        exact ⟨call', answers', true, hcfg', hval⟩
      · have hbase : Fact.done req val ∈
          (cfg.remove (Fact.need req' call') |>.add (Fact.finished req' call')) :=
          hold
        have hcfg : Fact.done req val ∈ cfg := by
          cases List.mem_cons.mp hbase with
          | inl h => cases h
          | inr h => exact List.mem_of_mem_erase h
        rcases hInv req val hcfg with ⟨call, answers, complete, htab, hval⟩
        have htrim : Fact.table call answers complete ∈ cfg.remove (Fact.need req' call') :=
          table_mem_erase_of_ne htab (by intro hEq; cases hEq)
        have hcfg' : Fact.table call answers complete ∈
            emitDoneFacts req' answers'
              (cfg.remove (Fact.need req' call') |>.add (Fact.finished req' call')) :=
          table_mem_emitDoneFacts_iff.mpr (List.mem_cons_of_mem _ htrim)
        exact ⟨call, answers, complete, hcfg', hval⟩
  | attachConsumer req' call' answers' cfg hNeed hTable =>
      rcases done_mem_emitDoneFacts_iff.mp hdone with hnew | hold
      · rcases hnew with ⟨hreq, hval⟩
        cases hreq
        have htrim : Fact.table call' answers' false ∈ cfg.remove (Fact.need req call') :=
          table_mem_erase_of_ne hTable (by intro hEq; cases hEq)
        have hcfg' : Fact.table call' answers' false ∈
            emitDoneFacts req answers'
              (cfg.remove (Fact.need req call') |>.add (Fact.waiting req call' answers')) :=
          table_mem_emitDoneFacts_iff.mpr (List.mem_cons_of_mem _ htrim)
        exact ⟨call', answers', false, hcfg', hval⟩
      · have hbase : Fact.done req val ∈
          (cfg.remove (Fact.need req' call') |>.add (Fact.waiting req' call' answers')) :=
          hold
        have hcfg : Fact.done req val ∈ cfg := by
          cases List.mem_cons.mp hbase with
          | inl h => cases h
          | inr h => exact List.mem_of_mem_erase h
        rcases hInv req val hcfg with ⟨call, answers, complete, htab, hval⟩
        have htrim : Fact.table call answers complete ∈ cfg.remove (Fact.need req' call') :=
          table_mem_erase_of_ne htab (by intro hEq; cases hEq)
        have hcfg' : Fact.table call answers complete ∈
            emitDoneFacts req' answers'
              (cfg.remove (Fact.need req' call') |>.add (Fact.waiting req' call' answers')) :=
          table_mem_emitDoneFacts_iff.mpr (List.mem_cons_of_mem _ htrim)
        exact ⟨call, answers, complete, hcfg', hval⟩
  | firstClaim req' call' cfg hNeed =>
      cases List.mem_cons.mp hdone with
      | inl h => cases h
      | inr h =>
          cases List.mem_cons.mp h with
          | inl h => cases h
          | inr h =>
              cases List.mem_cons.mp h with
              | inl h => cases h
              | inr h =>
                  rcases hInv req val (List.mem_of_mem_erase h) with ⟨call, answers, complete, htab, hval⟩
                  have htrim : Fact.table call answers complete ∈ cfg.remove (Fact.need req' call') :=
                    table_mem_erase_of_ne htab (by intro hEq; cases hEq)
                  exact ⟨call, answers, complete,
                    List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ htrim)),
                    hval⟩
  | driverSelect call' cfg hDriver hOpen =>
      cases List.mem_cons.mp hdone with
      | inl h => cases h
      | inr h =>
          rcases hInv req val (List.mem_of_mem_erase (List.mem_of_mem_erase h)) with
            ⟨call, answers, complete, htab, hval⟩
          have htrim1 : Fact.table call answers complete ∈ cfg.remove Fact.driverReady :=
            table_mem_erase_of_ne htab (by intro hEq; cases hEq)
          have htrim2 : Fact.table call answers complete ∈
              (cfg.remove Fact.driverReady).remove (Fact.open call') :=
            table_mem_erase_of_ne htrim1 (by intro hEq; cases hEq)
          exact ⟨call, answers, complete, List.mem_cons_of_mem _ htrim2, hval⟩
  | newAnswer call' answers' val' cfg hActive hTable hSem =>
      cases List.mem_cons.mp hdone with
      | inl h => cases h
      | inr h =>
          rcases hInv req val (List.mem_of_mem_erase h) with ⟨call, answers, complete, htab, hval⟩
          by_cases hsame : call = call' ∧ complete = false ∧ answers = answers'
          · rcases hsame with ⟨rfl, rfl, rfl⟩
            exact ⟨call, pushUniqueAnswer answers val', false, List.mem_cons_self,
              (mem_pushUniqueAnswer).2 (Or.inr hval)⟩
          · have hne : Fact.table call answers complete ≠ Fact.table call' answers' false := by
              intro hEq
              cases hEq
              exact hsame ⟨rfl, rfl, rfl⟩
            have htab' : Fact.table call answers complete ∈ cfg.remove (Fact.table call' answers' false) :=
              table_mem_erase_of_ne htab hne
            exact ⟨call, answers, complete, List.mem_cons_of_mem _ htab', hval⟩
  | dischargeAnswer req' call' seen answers' complete' val' cfg hWaiting hTable hIn hNotSeen =>
      cases List.mem_cons.mp hdone with
      | inl h =>
          cases h
          have htrim : Fact.table call' answers' complete' ∈ cfg.remove (Fact.waiting req call' seen) :=
            table_mem_erase_of_ne hTable (by intro hEq; cases hEq)
          exact ⟨call', answers', complete',
            List.mem_cons_of_mem _ (List.mem_cons_of_mem _ htrim), hIn⟩
      | inr h =>
          cases List.mem_cons.mp h with
          | inl h => cases h
          | inr h =>
              rcases hInv req val (List.mem_of_mem_erase h) with ⟨call, answers, complete, htab, hval⟩
              have htrim : Fact.table call answers complete ∈ cfg.remove (Fact.waiting req' call' seen) :=
                table_mem_erase_of_ne htab (by intro hEq; cases hEq)
              exact ⟨call, answers, complete,
                List.mem_cons_of_mem _ (List.mem_cons_of_mem _ htrim), hval⟩
  | completeCall call' answers' cfg hActive hTable =>
      cases List.mem_cons.mp hdone with
      | inl h => cases h
      | inr h =>
          cases List.mem_cons.mp h with
          | inl h => cases h
          | inr h =>
              rcases hInv req val (List.mem_of_mem_erase (List.mem_of_mem_erase h)) with
                ⟨call, answers, complete, htab, hval⟩
              by_cases hsame : call = call' ∧ complete = false ∧ answers = answers'
              · rcases hsame with ⟨rfl, rfl, rfl⟩
                exact ⟨call, answers, true, List.mem_cons_of_mem _ List.mem_cons_self, hval⟩
              · have hne : Fact.table call answers complete ≠ Fact.table call' answers' false := by
                  intro hEq
                  cases hEq
                  exact hsame ⟨rfl, rfl, rfl⟩
                have htrim1 : Fact.table call answers complete ∈ cfg.remove (Fact.active call') :=
                  table_mem_erase_of_ne htab (by intro hEq; cases hEq)
                have htrim2 : Fact.table call answers complete ∈
                    (cfg.remove (Fact.active call')).remove (Fact.table call' answers' false) :=
                  table_mem_erase_of_ne htrim1 hne
                exact ⟨call, answers, complete,
                  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ htrim2), hval⟩
  | finishWaiting req' call' seen answers' cfg hWaiting hTable hDelivered =>
      cases List.mem_cons.mp hdone with
      | inl h => cases h
      | inr h =>
          rcases hInv req val (List.mem_of_mem_erase h) with ⟨call, answers, complete, htab, hval⟩
          have htrim : Fact.table call answers complete ∈ cfg.remove (Fact.waiting req' call' seen) :=
            table_mem_erase_of_ne htab (by intro hEq; cases hEq)
          exact ⟨call, answers, complete, List.mem_cons_of_mem _ htrim, hval⟩

theorem doneBacked_reaches {cfg cfg' : Config}
    (hInv : DoneBacked cfg)
    (hReach : Reaches rules cfg cfg') :
    DoneBacked cfg' := by
  induction hReach with
  | refl => exact hInv
  | step hStep _ ih => exact ih (doneBacked_step hInv hStep)

theorem finishedBacked_step {cfg cfg' : Config}
    (hInv : FinishedBacked cfg)
    (hStep : Step rules cfg cfg') :
    FinishedBacked cfg' := by
  intro req call hfinished
  cases hStep with
  | tableHitComplete req' call' answers' cfg hNeed hTable =>
      have hbase :
          Fact.finished req call ∈
            (cfg.remove (Fact.need req' call') |>.add (Fact.finished req' call')) :=
        (finished_mem_emitDoneFacts_iff.mp hfinished)
      cases List.mem_cons.mp hbase with
      | inl h =>
          cases h
          have htrim : Fact.table call answers' true ∈ cfg.remove (Fact.need req call) :=
            table_mem_erase_of_ne hTable (by intro hEq; cases hEq)
          have hcfg' : Fact.table call answers' true ∈
              emitDoneFacts req answers'
                (cfg.remove (Fact.need req call) |>.add (Fact.finished req call)) :=
            table_mem_emitDoneFacts_iff.mpr (List.mem_cons_of_mem _ htrim)
          exact ⟨answers', hcfg'⟩
      | inr h =>
          have hcfg : Fact.finished req call ∈ cfg := List.mem_of_mem_erase h
          rcases hInv req call hcfg with ⟨answers, htab⟩
          have htrim : Fact.table call answers true ∈ cfg.remove (Fact.need req' call') :=
            table_mem_erase_of_ne htab (by intro hEq; cases hEq)
          have hcfg' : Fact.table call answers true ∈
              emitDoneFacts req' answers'
                (cfg.remove (Fact.need req' call') |>.add (Fact.finished req' call')) :=
            table_mem_emitDoneFacts_iff.mpr (List.mem_cons_of_mem _ htrim)
          exact ⟨answers, hcfg'⟩
  | attachConsumer req' call' answers' cfg hNeed hTable =>
      have hbase :
          Fact.finished req call ∈
            (cfg.remove (Fact.need req' call') |>.add (Fact.waiting req' call' answers')) :=
        (finished_mem_emitDoneFacts_iff.mp hfinished)
      cases List.mem_cons.mp hbase with
      | inl h => cases h
      | inr h =>
          rcases hInv req call (List.mem_of_mem_erase h) with ⟨answers, htab⟩
          have htrim : Fact.table call answers true ∈ cfg.remove (Fact.need req' call') :=
            table_mem_erase_of_ne htab (by intro hEq; cases hEq)
          have hcfg' : Fact.table call answers true ∈
              emitDoneFacts req' answers'
                (cfg.remove (Fact.need req' call') |>.add (Fact.waiting req' call' answers')) :=
            table_mem_emitDoneFacts_iff.mpr (List.mem_cons_of_mem _ htrim)
          exact ⟨answers, hcfg'⟩
  | firstClaim req' call' cfg hNeed =>
      cases List.mem_cons.mp hfinished with
      | inl h => cases h
      | inr h =>
          cases List.mem_cons.mp h with
          | inl h => cases h
          | inr h =>
              cases List.mem_cons.mp h with
              | inl h => cases h
              | inr h =>
                  rcases hInv req call (List.mem_of_mem_erase h) with ⟨answers, htab⟩
                  have htrim : Fact.table call answers true ∈ cfg.remove (Fact.need req' call') :=
                    table_mem_erase_of_ne htab (by intro hEq; cases hEq)
                  exact ⟨answers, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ htrim))⟩
  | driverSelect call' cfg hDriver hOpen =>
      have h1 :
          Fact.finished req call ∈
            (cfg.remove Fact.driverReady).remove (Fact.open call') := by
        cases List.mem_cons.mp hfinished with
        | inl h => cases h
        | inr h => exact h
      rcases hInv req call (List.mem_of_mem_erase (List.mem_of_mem_erase h1)) with ⟨answers, htab⟩
      have htrim1 : Fact.table call answers true ∈ cfg.remove Fact.driverReady :=
        table_mem_erase_of_ne htab (by intro hEq; cases hEq)
      have htrim2 : Fact.table call answers true ∈ (cfg.remove Fact.driverReady).remove (Fact.open call') :=
        table_mem_erase_of_ne htrim1 (by intro hEq; cases hEq)
      exact ⟨answers, List.mem_cons_of_mem _ htrim2⟩
  | newAnswer call' answers' val cfg hActive hTable hSem =>
      cases List.mem_cons.mp hfinished with
      | inl h => cases h
      | inr h =>
          have hcfg : Fact.finished req call ∈ cfg := List.mem_of_mem_erase h
          rcases hInv req call hcfg with ⟨answers, htab⟩
          have htab' : Fact.table call answers true ∈ cfg.erase (Fact.table call' answers' false) :=
            table_mem_erase_of_ne htab (by intro hEq; cases hEq)
          exact ⟨answers, List.mem_cons_of_mem _ htab'⟩
  | dischargeAnswer req' call' seen answers' complete' val cfg hWaiting hTable hIn hNotSeen =>
      have h1 : Fact.finished req call ∈ Fact.waiting req' call' (pushUniqueAnswer seen val) :: cfg.remove (Fact.waiting req' call' seen) := by
        cases List.mem_cons.mp hfinished with
        | inl h => cases h
        | inr h => exact h
      cases List.mem_cons.mp h1 with
      | inl h => cases h
      | inr h =>
          rcases hInv req call (List.mem_of_mem_erase h) with ⟨answers, htab⟩
          have htrim : Fact.table call answers true ∈ cfg.remove (Fact.waiting req' call' seen) :=
            table_mem_erase_of_ne htab (by intro hEq; cases hEq)
          exact ⟨answers, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ htrim)⟩
  | completeCall call' answers' cfg hActive hTable =>
      cases List.mem_cons.mp hfinished with
      | inl h => cases h
      | inr h =>
          cases List.mem_cons.mp h with
          | inl h => cases h
          | inr h =>
              have hcfg : Fact.finished req call ∈ cfg := List.mem_of_mem_erase (List.mem_of_mem_erase h)
              rcases hInv req call hcfg with ⟨answers, htab⟩
              have htab' : Fact.table call answers true ∈
                  (cfg.remove (Fact.active call')).remove (Fact.table call' answers' false) :=
                table_mem_erase_of_ne (table_mem_erase_of_ne htab (by intro hEq; cases hEq)) (by intro hEq; cases hEq)
              exact ⟨answers, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ htab')⟩
  | finishWaiting req' call' seen answers' cfg hWaiting hTable hDelivered =>
      cases List.mem_cons.mp hfinished with
      | inl h =>
          cases h
          have htrim : Fact.table call answers' true ∈ cfg.remove (Fact.waiting req call seen) :=
            table_mem_erase_of_ne hTable (by intro hEq; cases hEq)
          exact ⟨answers', List.mem_cons_of_mem _ htrim⟩
      | inr h =>
          rcases hInv req call (List.mem_of_mem_erase h) with ⟨answers, htab⟩
          have htrim : Fact.table call answers true ∈ cfg.remove (Fact.waiting req' call' seen) :=
            table_mem_erase_of_ne htab (by intro hEq; cases hEq)
          exact ⟨answers, List.mem_cons_of_mem _ htrim⟩

theorem finishedBacked_reaches {cfg cfg' : Config}
    (hInv : FinishedBacked cfg)
    (hReach : Reaches rules cfg cfg') :
    FinishedBacked cfg' := by
  induction hReach with
  | refl => exact hInv
  | step hStep _ ih => exact ih (finishedBacked_step hInv hStep)

/-- Admissible configs for the current finite-answer tabling fragment.

Positive example: sound tables, backed `done`/`finished` facts, and monotone
table growth are all present together.
Negative example: this is not yet a full SLG admissibility theorem with SCC
eligibility and infinite-answer handling. -/
def TablingAdmissible (rules : List EvalRule) (cfg : Config) : Prop :=
  TableSound rules cfg ∧
  DoneBacked cfg ∧
  FinishedBacked cfg ∧
  ∀ {cfg'}, Reaches rules cfg cfg' → TableAnswersGrow cfg cfg'

theorem tablingAdmissible_initial (root : CallKey) :
    TablingAdmissible rules (initialConfig root) := by
  refine ⟨tableSound_initial root, doneBacked_initial root, finishedBacked_initial root, ?_⟩
  intro cfg' hReach
  exact tableAnswersGrow_reaches hReach

theorem tablingAdmissible_reaches {cfg cfg' : Config}
    (hInv : TablingAdmissible rules cfg)
    (hReach : Reaches rules cfg cfg') :
    TablingAdmissible rules cfg' := by
  rcases hInv with ⟨hSound, hDone, hFinished, _hGrow⟩
  refine ⟨
    tableSound_reaches hSound hReach,
    doneBacked_reaches hDone hReach,
    finishedBacked_reaches hFinished hReach,
    ?_⟩
  intro cfg'' hReach'
  exact tableAnswersGrow_reaches hReach'

theorem sealPlan_reaches_admissible
    {rules : List EvalRule} {cfg : Config} {plan : SealPlan}
    (hAdm : TablingAdmissible rules cfg)
    (hDistinct : PlanDistinct plan)
    (hReady : PlanReady cfg plan) :
    ∃ cfg',
      Reaches rules cfg cfg' ∧
      PlanSealed cfg' plan ∧
      TablingAdmissible rules cfg' := by
  rcases sealPlan_reaches (rules := rules) (cfg := cfg) (plan := plan) hDistinct hReady with
    ⟨cfg', hLocal, hSealed, _hPreserve⟩
  exact ⟨cfg', hLocal, hSealed, tablingAdmissible_reaches hAdm hLocal⟩

theorem sealPlan_of_reaches_admissible
    {rules : List EvalRule} {root : CallKey} {cfg : Config} {plan : SealPlan}
    (hReach : Reaches rules (initialConfig root) cfg)
    (hDistinct : PlanDistinct plan)
    (hReady : PlanReady cfg plan) :
    ∃ cfg',
      Reaches rules (initialConfig root) cfg' ∧
      PlanSealed cfg' plan ∧
      TablingAdmissible rules cfg' := by
  have hAdmCfg : TablingAdmissible rules cfg :=
    tablingAdmissible_reaches (rules := rules) (tablingAdmissible_initial root) hReach
  rcases sealPlan_reaches_admissible (rules := rules) (cfg := cfg) (plan := plan)
      hAdmCfg hDistinct hReady with
    ⟨cfg', hLocal, hSealed, hAdm'⟩
  exact ⟨cfg', Reaches.trans hReach hLocal, hSealed, hAdm'⟩

theorem finiteCyclicEligible_of_reaches_admissible
    {rules : List EvalRule} {root : CallKey} {cfg : Config} {plan : SealPlan}
    (hReach : Reaches rules (initialConfig root) cfg)
    (hEligible : FiniteCyclicEligible cfg plan) :
    ∃ cfg',
      Reaches rules (initialConfig root) cfg' ∧
      PlanSealed cfg' plan ∧
      TablingAdmissible rules cfg' := by
  exact sealPlan_of_reaches_admissible
    (rules := rules) (root := root) (cfg := cfg) (plan := plan)
    hReach hEligible.1 hEligible.2

theorem closedFiniteCyclicEligible_of_reaches_admissible
    {rules : List EvalRule} {root : CallKey} {cfg : Config} {plan : SealPlan}
    (hReach : Reaches rules (initialConfig root) cfg)
    (hEligible : ClosedFiniteCyclicEligible cfg plan) :
    ∃ cfg',
      Reaches rules (initialConfig root) cfg' ∧
      PlanSealed cfg' plan ∧
      TablingAdmissible rules cfg' := by
  exact finiteCyclicEligible_of_reaches_admissible
    (rules := rules) (root := root) (cfg := cfg) (plan := plan)
    hReach hEligible.1

private theorem planCoversActive_answers_mem
    {cfg : Config} {plan : SealPlan} {call : CallKey}
    (hCover : PlanCoversActive cfg plan)
    (hActive : Fact.active call ∈ cfg) :
    ∃ answers, (call, answers) ∈ plan := by
  have hCall : call ∈ plan.map Prod.fst := hCover hActive
  rcases List.mem_map.mp hCall with ⟨entry, hEntry, hEq⟩
  rcases entry with ⟨call', answers⟩
  dsimp at hEq
  subst hEq
  exact ⟨answers, hEntry⟩

theorem closedFiniteCyclicEligible_of_reaches_active_complete_admissible
    {rules : List EvalRule} {root : CallKey} {cfg : Config} {plan : SealPlan}
    {call : CallKey}
    (hReach : Reaches rules (initialConfig root) cfg)
    (hEligible : ClosedFiniteCyclicEligible cfg plan)
    (hActive : Fact.active call ∈ cfg) :
    ∃ cfg' answers,
      Reaches rules (initialConfig root) cfg' ∧
      PlanSealed cfg' plan ∧
      Fact.table call answers true ∈ cfg' ∧
      TablingAdmissible rules cfg' := by
  rcases planCoversActive_answers_mem hEligible.2 hActive with ⟨answers, hPlan⟩
  rcases closedFiniteCyclicEligible_of_reaches_admissible
      (rules := rules) (root := root) (cfg := cfg) (plan := plan)
      hReach hEligible with
    ⟨cfg', hReach', hSealed, hAdm'⟩
  exact ⟨cfg', answers, hReach', hSealed, hSealed hPlan, hAdm'⟩

theorem sealPlan_reaches_preserves_waiting
    {rules : List EvalRule} :
    ∀ {cfg : Config} {plan : SealPlan} {req : ReqId} {call : CallKey} {seen : List EvalValue},
      PlanDistinct plan →
      PlanReady cfg plan →
      Fact.waiting req call seen ∈ cfg →
      ∃ cfg',
        Reaches rules cfg cfg' ∧
        PlanSealed cfg' plan ∧
        Fact.waiting req call seen ∈ cfg' ∧
        (∀ call answers,
          Fact.table call answers true ∈ cfg →
            Fact.table call answers true ∈ cfg') := by
  intro cfg plan req call seen hDistinct hReady hWaiting
  induction plan generalizing cfg with
  | nil =>
      refine ⟨cfg, Reaches.refl, ?_, hWaiting, ?_⟩
      · intro call answers hMem
        cases hMem
      · intro call answers hMem
        exact hMem
  | cons head tail ih =>
      rcases head with ⟨call₀, answers₀⟩
      have hDistinctMap : (List.map Prod.fst ((call₀, answers₀) :: tail)).Nodup := by
        simpa [PlanDistinct] using hDistinct
      rcases List.nodup_cons.mp hDistinctMap with ⟨hNotInTail, hTailDistinctMap⟩
      have hTailDistinct : PlanDistinct tail := by
        simpa [PlanDistinct] using hTailDistinctMap
      have hHeadReady : Fact.active call₀ ∈ cfg ∧ Fact.table call₀ answers₀ false ∈ cfg :=
        hReady (by simp)
      rcases hHeadReady with ⟨hActive, hTable⟩
      let cfg₁ : Config :=
        (cfg.remove (Fact.active call₀)
          |>.remove (Fact.table call₀ answers₀ false)
          |>.add (Fact.table call₀ answers₀ true)
          |>.add Fact.driverReady)
      have hStep : Step rules cfg cfg₁ :=
        Step.completeCall call₀ answers₀ cfg hActive hTable
      have hWaiting₁ : Fact.waiting req call seen ∈ cfg₁ := by
        apply fact_mem_completeCall_cfg_of_ne hWaiting
        · intro hEq
          cases hEq
        · intro hEq
          cases hEq
      have hComplete₁ : Fact.table call₀ answers₀ true ∈ cfg₁ :=
        completeCall_complete_table_mem call₀ answers₀ cfg
      have hTailReady : PlanReady cfg₁ tail := by
        intro call' answers' hMem
        have hOrig : (call', answers') ∈ (call₀, answers₀) :: tail :=
          List.mem_cons_of_mem _ hMem
        have hOrigReady : Fact.active call' ∈ cfg ∧ Fact.table call' answers' false ∈ cfg :=
          hReady hOrig
        have hCallMem : call' ∈ tail.map Prod.fst := by
          exact List.mem_map.mpr ⟨(call', answers'), hMem, rfl⟩
        have hNe : call' ≠ call₀ := by
          intro hEq
          apply hNotInTail
          simpa [hEq] using hCallMem
        exact ⟨
          active_mem_completeCall_cfg_of_ne hOrigReady.1 hNe,
          open_table_mem_completeCall_cfg_of_ne hOrigReady.2 hNe
        ⟩
      rcases ih hTailDistinct hTailReady hWaiting₁ with
        ⟨cfg₂, hTailReach, hTailSealed, hWaiting₂, hPreserve⟩
      have hHeadSealed : Fact.table call₀ answers₀ true ∈ cfg₂ :=
        hPreserve call₀ answers₀ hComplete₁
      refine ⟨cfg₂, Reaches.step hStep hTailReach, ?_, hWaiting₂, ?_⟩
      · intro call' answers' hMem
        cases List.mem_cons.mp hMem with
        | inl hEq =>
            cases hEq
            exact hHeadSealed
        | inr hTail =>
            exact hTailSealed hTail
      · intro call' answers' hMem
        exact hPreserve call' answers' (complete_table_mem_completeCall_cfg hMem)

private theorem planSealed_preserved_by_finishWaiting
    {plan : SealPlan} {cfg : Config}
    {req : ReqId} {call : CallKey} {seen : List EvalValue}
    (hSealed : PlanSealed cfg plan) :
    PlanSealed (cfg.remove (Fact.waiting req call seen) |>.add (Fact.finished req call)) plan := by
  intro call' answers' hMem
  have hBase : Fact.table call' answers' true ∈ cfg := hSealed hMem
  have hTrim : Fact.table call' answers' true ∈ cfg.remove (Fact.waiting req call seen) :=
    fact_mem_erase_of_ne hBase (by intro hEq; cases hEq)
  exact List.mem_cons_of_mem _ hTrim

private theorem planSealed_preserved_by_dischargeAnswer
    {plan : SealPlan} {cfg : Config}
    {req : ReqId} {call : CallKey} {seen : List EvalValue}
    {val : EvalValue}
    (hSealed : PlanSealed cfg plan) :
    PlanSealed
      (Fact.done req val ::
        Fact.waiting req call (pushUniqueAnswer seen val) :: cfg.remove (Fact.waiting req call seen))
      plan := by
  intro call' answers' hMem
  have hBase : Fact.table call' answers' true ∈ cfg := hSealed hMem
  have hTrim : Fact.table call' answers' true ∈ cfg.remove (Fact.waiting req call seen) :=
    fact_mem_erase_of_ne hBase (by intro hEq; cases hEq)
  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hTrim)

theorem sealPlan_reaches_finish_waiting_admissible
    {rules : List EvalRule} {cfg : Config} {plan : SealPlan}
    {req : ReqId} {call : CallKey} {seen answers : List EvalValue}
    (hAdm : TablingAdmissible rules cfg)
    (hDistinct : PlanDistinct plan)
    (hReady : PlanReady cfg plan)
    (hPlan : (call, answers) ∈ plan)
    (hWaiting : Fact.waiting req call seen ∈ cfg)
    (hDelivered : DeliveredAll answers seen) :
    ∃ cfg',
      Reaches rules cfg cfg' ∧
      PlanSealed cfg' plan ∧
      Fact.finished req call ∈ cfg' ∧
      TablingAdmissible rules cfg' := by
  rcases sealPlan_reaches_preserves_waiting
      (rules := rules) (cfg := cfg) (plan := plan)
      (req := req) (call := call) (seen := seen)
      hDistinct hReady hWaiting with
    ⟨cfg₁, hSealReach, hSealed, hWaiting₁, _hPreserve⟩
  have hTable₁ : Fact.table call answers true ∈ cfg₁ := hSealed hPlan
  let cfg₂ : Config := cfg₁.remove (Fact.waiting req call seen) |>.add (Fact.finished req call)
  have hStep : Step rules cfg₁ cfg₂ :=
    Step.finishWaiting req call seen answers cfg₁ hWaiting₁ hTable₁ hDelivered
  have hFinished : Fact.finished req call ∈ cfg₂ :=
    finishWaiting_finished_mem req call seen answers cfg₁
  have hReach₂ : Reaches rules cfg cfg₂ :=
    Reaches.trans hSealReach (Reaches.step hStep Reaches.refl)
  have hSealed₂ : PlanSealed cfg₂ plan := by
    exact planSealed_preserved_by_finishWaiting hSealed
  have hAdm₂ : TablingAdmissible rules cfg₂ :=
    tablingAdmissible_reaches hAdm hReach₂
  exact ⟨cfg₂, hReach₂, hSealed₂, hFinished, hAdm₂⟩

theorem closedFiniteCyclicEligible_of_reaches_waiting_active_complete_admissible
    {rules : List EvalRule} {root : CallKey} {cfg : Config} {plan : SealPlan}
    {req : ReqId} {call : CallKey} {seen : List EvalValue}
    (hReach : Reaches rules (initialConfig root) cfg)
    (hEligible : ClosedFiniteCyclicEligible cfg plan)
    (hWaiting : Fact.waiting req call seen ∈ cfg)
    (hActive : Fact.active call ∈ cfg) :
    ∃ cfg' answers,
      Reaches rules (initialConfig root) cfg' ∧
      PlanSealed cfg' plan ∧
      Fact.waiting req call seen ∈ cfg' ∧
      Fact.table call answers true ∈ cfg' ∧
      TablingAdmissible rules cfg' := by
  have hAdm : TablingAdmissible rules cfg :=
    tablingAdmissible_reaches (rules := rules) (tablingAdmissible_initial root) hReach
  rcases planCoversActive_answers_mem hEligible.2 hActive with ⟨answers, hPlan⟩
  rcases sealPlan_reaches_preserves_waiting
      (rules := rules) (cfg := cfg) (plan := plan)
      (req := req) (call := call) (seen := seen)
      hEligible.1.1 hEligible.1.2 hWaiting with
    ⟨cfg', hLocal, hSealed, hWaiting', _hPreserve⟩
  have hReach' : Reaches rules (initialConfig root) cfg' :=
    Reaches.trans hReach hLocal
  have hAdm' : TablingAdmissible rules cfg' :=
    tablingAdmissible_reaches (rules := rules) (tablingAdmissible_initial root) hReach'
  exact ⟨cfg', answers, hReach', hSealed, hWaiting', hSealed hPlan, hAdm'⟩

theorem finiteCyclicEligible_of_reaches_finish_waiting_complete_admissible
    {rules : List EvalRule} {root : CallKey} {cfg : Config} {plan : SealPlan}
    {req : ReqId} {call : CallKey} {seen answers : List EvalValue}
    (hReach : Reaches rules (initialConfig root) cfg)
    (hEligible : FiniteCyclicEligible cfg plan)
    (hPlan : (call, answers) ∈ plan)
    (hWaiting : Fact.waiting req call seen ∈ cfg)
    (hDelivered : DeliveredAll answers seen) :
    ∃ cfg',
      Reaches rules (initialConfig root) cfg' ∧
      PlanSealed cfg' plan ∧
      Fact.finished req call ∈ cfg' ∧
      Fact.table call answers true ∈ cfg' ∧
      TablingAdmissible rules cfg' := by
  have hAdm : TablingAdmissible rules cfg :=
    tablingAdmissible_reaches (rules := rules) (tablingAdmissible_initial root) hReach
  rcases sealPlan_reaches_finish_waiting_admissible
      (rules := rules) (cfg := cfg) (plan := plan)
      (req := req) (call := call) (seen := seen) (answers := answers)
      hAdm hEligible.1 hEligible.2 hPlan hWaiting hDelivered with
    ⟨cfg', hLocal, hSealed, hFinished, hAdm'⟩
  exact ⟨cfg', Reaches.trans hReach hLocal, hSealed, hFinished, hSealed hPlan, hAdm'⟩

theorem closedFiniteCyclicEligible_of_reaches_finish_waiting_complete_admissible
    {rules : List EvalRule} {root : CallKey} {cfg : Config} {plan : SealPlan}
    {req : ReqId} {call : CallKey} {seen answers : List EvalValue}
    (hReach : Reaches rules (initialConfig root) cfg)
    (hEligible : ClosedFiniteCyclicEligible cfg plan)
    (hPlan : (call, answers) ∈ plan)
    (hWaiting : Fact.waiting req call seen ∈ cfg)
    (hDelivered : DeliveredAll answers seen) :
    ∃ cfg',
      Reaches rules (initialConfig root) cfg' ∧
      PlanSealed cfg' plan ∧
      Fact.finished req call ∈ cfg' ∧
      Fact.table call answers true ∈ cfg' ∧
      TablingAdmissible rules cfg' := by
  exact finiteCyclicEligible_of_reaches_finish_waiting_complete_admissible
    (rules := rules) (root := root) (cfg := cfg) (plan := plan)
    hReach hEligible.1 hPlan hWaiting hDelivered

theorem finiteCyclicEligible_of_reaches_discharge_answer_sound_admissible
    {rules : List EvalRule} {root : CallKey} {cfg : Config} {plan : SealPlan}
    {req : ReqId} {call : CallKey} {seen answers : List EvalValue} {val : EvalValue}
    (hReach : Reaches rules (initialConfig root) cfg)
    (hEligible : FiniteCyclicEligible cfg plan)
    (hPlan : (call, answers) ∈ plan)
    (hWaiting : Fact.waiting req call seen ∈ cfg)
    (hVal : val ∈ answers)
    (hFresh : val ∉ seen) :
    ∃ cfg' call',
      Reaches rules (initialConfig root) cfg' ∧
      PlanSealed cfg' plan ∧
      Fact.waiting req call (pushUniqueAnswer seen val) ∈ cfg' ∧
      Fact.done req val ∈ cfg' ∧
      EvalSem rules (callNode call') val ∧
      TablingAdmissible rules cfg' := by
  rcases sealPlan_reaches_preserves_waiting
      (rules := rules) (cfg := cfg) (plan := plan)
      (req := req) (call := call) (seen := seen)
      hEligible.1 hEligible.2 hWaiting with
    ⟨cfg₁, hSealLocal, hSealed, hWaiting₁, _hPreserve⟩
  have hReach₁ : Reaches rules (initialConfig root) cfg₁ :=
    Reaches.trans hReach hSealLocal
  have hTable₁ : Fact.table call answers true ∈ cfg₁ := hSealed hPlan
  let cfg₂ : Config :=
    cfg₁.remove (Fact.waiting req call seen)
      |>.add (Fact.waiting req call (pushUniqueAnswer seen val))
      |>.add (Fact.done req val)
  have hStep₂ : Step rules cfg₁ cfg₂ :=
    Step.dischargeAnswer req call seen answers true val cfg₁ hWaiting₁ hTable₁ hVal hFresh
  have hWaiting₂ : Fact.waiting req call (pushUniqueAnswer seen val) ∈ cfg₂ :=
    dischargeAnswer_waiting_mem req call seen val cfg₁
  have hDone₂ : Fact.done req val ∈ cfg₂ :=
    dischargeAnswer_done_mem req call seen val cfg₁
  have hLocal₂ : Reaches rules cfg₁ cfg₂ :=
    Reaches.step hStep₂ Reaches.refl
  have hReach₂ : Reaches rules (initialConfig root) cfg₂ :=
    Reaches.trans hReach₁ hLocal₂
  obtain ⟨call', answers', complete', hTable₂, hMem₂⟩ :=
    doneBacked_reaches (doneBacked_initial root) hReach₂ req val hDone₂
  have hSem : EvalSem rules (callNode call') val :=
    tableSound_reaches (tableSound_initial root) hReach₂ call' answers' complete' hTable₂ val hMem₂
  have hSealed₂ : PlanSealed cfg₂ plan := by
    exact planSealed_preserved_by_dischargeAnswer hSealed
  have hAdm₂ : TablingAdmissible rules cfg₂ :=
    tablingAdmissible_reaches (rules := rules) (tablingAdmissible_initial root) hReach₂
  exact ⟨cfg₂, call', hReach₂, hSealed₂, hWaiting₂, hDone₂, hSem, hAdm₂⟩

theorem closedFiniteCyclicEligible_of_reaches_discharge_answer_sound_admissible
    {rules : List EvalRule} {root : CallKey} {cfg : Config} {plan : SealPlan}
    {req : ReqId} {call : CallKey} {seen answers : List EvalValue} {val : EvalValue}
    (hReach : Reaches rules (initialConfig root) cfg)
    (hEligible : ClosedFiniteCyclicEligible cfg plan)
    (hPlan : (call, answers) ∈ plan)
    (hWaiting : Fact.waiting req call seen ∈ cfg)
    (hVal : val ∈ answers)
    (hFresh : val ∉ seen) :
    ∃ cfg' call',
      Reaches rules (initialConfig root) cfg' ∧
      PlanSealed cfg' plan ∧
      Fact.waiting req call (pushUniqueAnswer seen val) ∈ cfg' ∧
      Fact.done req val ∈ cfg' ∧
      EvalSem rules (callNode call') val ∧
      TablingAdmissible rules cfg' := by
  exact finiteCyclicEligible_of_reaches_discharge_answer_sound_admissible
    (rules := rules) (root := root) (cfg := cfg) (plan := plan)
    hReach hEligible.1 hPlan hWaiting hVal hFresh

theorem finiteCyclicEligible_of_reaches_discharge_then_finish_sound_complete_admissible
    {rules : List EvalRule} {root : CallKey} {cfg : Config} {plan : SealPlan}
    {req : ReqId} {call : CallKey} {seen answers : List EvalValue} {val : EvalValue}
    (hReach : Reaches rules (initialConfig root) cfg)
    (hEligible : FiniteCyclicEligible cfg plan)
    (hPlan : (call, answers) ∈ plan)
    (hWaiting : Fact.waiting req call seen ∈ cfg)
    (hVal : val ∈ answers)
    (hFresh : val ∉ seen)
    (hDelivered : DeliveredAll answers (pushUniqueAnswer seen val)) :
    ∃ cfg' call',
      Reaches rules (initialConfig root) cfg' ∧
      PlanSealed cfg' plan ∧
      Fact.done req val ∈ cfg' ∧
      Fact.finished req call ∈ cfg' ∧
      Fact.table call answers true ∈ cfg' ∧
      EvalSem rules (callNode call') val ∧
      TablingAdmissible rules cfg' := by
  rcases finiteCyclicEligible_of_reaches_discharge_answer_sound_admissible
      (rules := rules) (root := root) (cfg := cfg) (plan := plan)
      (req := req) (call := call) (seen := seen) (answers := answers) (val := val)
      hReach hEligible hPlan hWaiting hVal hFresh with
    ⟨cfg₁, call', hReach₁, hSealed₁, hWaiting₁, hDone₁, hSem₁, hAdm₁⟩
  have hTable₁ : Fact.table call answers true ∈ cfg₁ := hSealed₁ hPlan
  let cfg₂ : Config :=
    cfg₁.remove (Fact.waiting req call (pushUniqueAnswer seen val))
      |>.add (Fact.finished req call)
  have hStep₂ : Step rules cfg₁ cfg₂ :=
    Step.finishWaiting req call (pushUniqueAnswer seen val) answers cfg₁ hWaiting₁ hTable₁ hDelivered
  have hFinished₂ : Fact.finished req call ∈ cfg₂ :=
    finishWaiting_finished_mem req call (pushUniqueAnswer seen val) answers cfg₁
  have hLocal₂ : Reaches rules cfg₁ cfg₂ :=
    Reaches.step hStep₂ Reaches.refl
  have hReach₂ : Reaches rules (initialConfig root) cfg₂ :=
    Reaches.trans hReach₁ hLocal₂
  have hSealed₂ : PlanSealed cfg₂ plan := by
    exact planSealed_preserved_by_finishWaiting hSealed₁
  have hDoneTrim :
      Fact.done req val ∈ cfg₁.remove (Fact.waiting req call (pushUniqueAnswer seen val)) :=
    fact_mem_erase_of_ne hDone₁ (by intro hEq; cases hEq)
  have hDone₂ : Fact.done req val ∈ cfg₂ :=
    List.mem_cons_of_mem _ hDoneTrim
  have hAdm₂ : TablingAdmissible rules cfg₂ :=
    tablingAdmissible_reaches hAdm₁ hLocal₂
  exact ⟨cfg₂, call', hReach₂, hSealed₂, hDone₂, hFinished₂, hSealed₂ hPlan, hSem₁, hAdm₂⟩

theorem closedFiniteCyclicEligible_of_reaches_discharge_then_finish_sound_complete_admissible
    {rules : List EvalRule} {root : CallKey} {cfg : Config} {plan : SealPlan}
    {req : ReqId} {call : CallKey} {seen answers : List EvalValue} {val : EvalValue}
    (hReach : Reaches rules (initialConfig root) cfg)
    (hEligible : ClosedFiniteCyclicEligible cfg plan)
    (hPlan : (call, answers) ∈ plan)
    (hWaiting : Fact.waiting req call seen ∈ cfg)
    (hVal : val ∈ answers)
    (hFresh : val ∉ seen)
    (hDelivered : DeliveredAll answers (pushUniqueAnswer seen val)) :
    ∃ cfg' call',
      Reaches rules (initialConfig root) cfg' ∧
      PlanSealed cfg' plan ∧
      Fact.done req val ∈ cfg' ∧
      Fact.finished req call ∈ cfg' ∧
      Fact.table call answers true ∈ cfg' ∧
      EvalSem rules (callNode call') val ∧
      TablingAdmissible rules cfg' := by
  exact finiteCyclicEligible_of_reaches_discharge_then_finish_sound_complete_admissible
    (rules := rules) (root := root) (cfg := cfg) (plan := plan)
    hReach hEligible.1 hPlan hWaiting hVal hFresh hDelivered

theorem finished_complete_table_of_reaches
    {root : CallKey} {cfg : Config} {req : ReqId} {call : CallKey}
    (hReach : Reaches rules (initialConfig root) cfg)
    (hFinished : Fact.finished req call ∈ cfg) :
    ∃ answers, Fact.table call answers true ∈ cfg :=
  finishedBacked_reaches (finishedBacked_initial root) hReach req call hFinished

theorem tabling_done_sound
    {rules : List EvalRule} {root : CallKey} {cfg : Config}
    (hReach : Reaches rules (initialConfig root) cfg)
    (req : ReqId) (val : EvalValue)
    (hDone : Fact.done req val ∈ cfg) :
    ∃ call : CallKey, EvalSem rules (callNode call) val := by
  obtain ⟨call, answers, complete, htab, hmem⟩ :=
    doneBacked_reaches (doneBacked_initial root) hReach req val hDone
  have hSound : EvalSem rules (callNode call) val :=
    tableSound_reaches (tableSound_initial root) hReach call answers complete htab val hmem
  exact ⟨call, hSound⟩

theorem waiting_progress_discharge_sound_of_reaches
    {rules : List EvalRule} {root : CallKey} {cfg : Config}
    {req : ReqId} {call : CallKey} {seen answers : List EvalValue}
    {complete : Bool} {val : EvalValue}
    (hReach : Reaches rules (initialConfig root) cfg)
    (hWaiting : Fact.waiting req call seen ∈ cfg)
    (hTable : Fact.table call answers complete ∈ cfg)
    (hVal : val ∈ answers)
    (hFresh : val ∉ seen) :
    ∃ cfg' call',
      Reaches rules (initialConfig root) cfg' ∧
      Fact.waiting req call (pushUniqueAnswer seen val) ∈ cfg' ∧
      Fact.done req val ∈ cfg' ∧
      EvalSem rules (callNode call') val := by
  rcases waiting_progress_discharge_of_reaches
      (rules := rules) (root := root) hReach hWaiting hTable hVal hFresh with
    ⟨cfg', hLocal, hWaiting', hDone⟩
  have hReach' : Reaches rules (initialConfig root) cfg' :=
    Reaches.trans hReach hLocal
  obtain ⟨call', hSem⟩ := tabling_done_sound hReach' req val hDone
  exact ⟨cfg', call', hReach', hWaiting', hDone, hSem⟩

theorem waiting_progress_finish_backed_of_reaches
    {rules : List EvalRule} {root : CallKey} {cfg : Config}
    {req : ReqId} {call : CallKey} {seen answers : List EvalValue}
    (hReach : Reaches rules (initialConfig root) cfg)
    (hWaiting : Fact.waiting req call seen ∈ cfg)
    (hTable : Fact.table call answers true ∈ cfg)
    (hDelivered : DeliveredAll answers seen) :
    ∃ cfg' answers',
      Reaches rules (initialConfig root) cfg' ∧
      Fact.finished req call ∈ cfg' ∧
      Fact.table call answers' true ∈ cfg' := by
  rcases waiting_progress_finish_of_reaches
      (rules := rules) (root := root) hReach hWaiting hTable hDelivered with
    ⟨cfg', hLocal, hFinished⟩
  have hReach' : Reaches rules (initialConfig root) cfg' :=
    Reaches.trans hReach hLocal
  obtain ⟨answers', hComplete⟩ := finished_complete_table_of_reaches hReach' hFinished
  exact ⟨cfg', answers', hReach', hFinished, hComplete⟩

end MeTTailCore.EvalIRTablingMachine
