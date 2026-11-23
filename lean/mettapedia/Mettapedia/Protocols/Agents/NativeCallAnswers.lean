import Mathlib.Tactic
import Mettapedia.Protocols.Agents.NativeCallOwner

/-!
# What a native provider call answers with

A call's kind (a command or a structured request) and its ledger purpose
(a turn, a coding step or a compaction) are fixed when the call is prepared.
Delivery of a completed result depends only on those facts:

* a command turn answers with a program, after the command contract has
  classified the result; a rejected classification is an empty answer;
* a structured call, and any compaction, answers with its reply (the first
  choice's message, its finish reason and usage); the command contract is
  never consulted.

A refused preparation is not an owner: it is the owner phase `refused`, from
which no event submits.

Invariants proved here:
* a structured or compaction call's completed result is delivered as its
  reply, whatever the command contract would say about it;
* a command turn never yields a reply;
* every ledger record of a call carries the purpose fixed at preparation;
* a refused preparation never submits.

Counterexamples, each the rule the port replaced:
* "a native owner is always a command": a structured call's tool-call reply
  goes through the command contract, which rejects it, so a completed coding
  step is delivered as an empty, failed turn;
* a purpose set on the host plan after it exists: a call admitted as a turn
  can settle as a coding step, so its ledger records disagree.

This is an abstract contract. It is not a refinement proof of the MeTTa owner,
of the provider ledger or of the host effects.
-/

set_option autoImplicit false

namespace Mettapedia.Protocols.Agents.NativeCallAnswers

inductive Kind where
  | command | structured
  deriving DecidableEq

inductive Purpose where
  | turn | coding | compaction
  deriving DecidableEq

/-- The facts a call keeps from its preparation on. -/
structure Facts where
  kind : Kind
  purpose : Purpose
  deriving DecidableEq

/-- The command contract applies to a command turn and to nothing else. -/
def ContractApplies (f : Facts) : Prop := f.kind = .command ∧ f.purpose = .turn

instance (f : Facts) : Decidable (ContractApplies f) := by
  unfold ContractApplies; infer_instance

inductive Answer (Program Reply : Type) where
  | program (p : Program)
  | reply (r : Reply)
  | empty
  deriving DecidableEq

variable {Result Program Reply : Type}

/-- The delivery rule. `classify` is the command contract (`none` is a
rejection); `project` builds the reply of a completed result. -/
def deliver (classify : Result → Option Program) (project : Result → Reply)
    (f : Facts) (r : Result) : Answer Program Reply :=
  if ContractApplies f then
    match classify r with
    | some p => .program p
    | none => .empty
  else .reply (project r)

theorem replies_unless_command_turn (classify : Result → Option Program)
    (project : Result → Reply) {f : Facts} (h : ¬ ContractApplies f) (r : Result) :
    deliver classify project f r = .reply (project r) := by
  simp [deliver, h]

/-- A structured call's completed result is always its reply. -/
theorem structured_replies (classify : Result → Option Program) (project : Result → Reply)
    {f : Facts} (h : f.kind = .structured) (r : Result) :
    deliver classify project f r = .reply (project r) :=
  replies_unless_command_turn classify project (by simp [ContractApplies, h]) r

/-- A compaction, whatever its kind, answers with its reply. -/
theorem compaction_replies (classify : Result → Option Program) (project : Result → Reply)
    {f : Facts} (h : f.purpose = .compaction) (r : Result) :
    deliver classify project f r = .reply (project r) :=
  replies_unless_command_turn classify project (by simp [ContractApplies, h]) r

/-- A command turn never yields a reply: its answer is a program or empty. -/
theorem command_turn_never_replies (classify : Result → Option Program)
    (project : Result → Reply) {f : Facts} (h : ContractApplies f) (r : Result) (x : Reply) :
    deliver classify project f r ≠ .reply x := by
  unfold deliver
  rw [if_pos h]
  cases classify r <;> simp

/-- The retired rule: every native owner is a command. -/
def deliverAsCommand (classify : Result → Option Program) (_project : Result → Reply)
    (_f : Facts) (r : Result) : Answer Program Reply :=
  match classify r with
  | some p => .program p
  | none => .empty

/-- Under the retired rule, a structured result the command contract rejects
(for example a tool call to a coding tool) is delivered empty, where the
owned rule delivers it as the call's reply. -/
theorem command_rule_loses_structured_replies (classify : Result → Option Program)
    (project : Result → Reply) (r : Result) (rejected : classify r = none) :
    let f : Facts := ⟨.structured, .coding⟩
    deliverAsCommand classify project f r = .empty ∧
      deliver classify project f r = .reply (project r) := by
  refine ⟨by simp [deliverAsCommand, rejected], structured_replies classify project rfl r⟩

/-! ## The purpose recorded for a call -/

/-- Events of a call that write a ledger record, and the retired retargeting. -/
inductive Event where
  | admit | describe | settle
  | retarget (p : Purpose)

/-- The owned design: the facts are immutable, so a retargeting has no rule
and every record carries the captured purpose. -/
def recordsFixed (f : Facts) : List Event → List Purpose
  | [] => []
  | .retarget _ :: es => recordsFixed f es
  | _ :: es => f.purpose :: recordsFixed f es

theorem fixed_records_carry_the_prepared_purpose (f : Facts) (es : List Event) :
    ∀ p ∈ recordsFixed f es, p = f.purpose := by
  induction es with
  | nil => simp [recordsFixed]
  | cons e es ih =>
    cases e with
    | retarget q => exact ih
    | admit | describe | settle =>
      intro p hp
      rcases List.mem_cons.mp hp with rfl | hp
      · rfl
      · exact ih p hp

/-- The retired design: a host plan's purpose could be set after it existed. -/
def recordsMutable (p : Purpose) : List Event → List Purpose
  | [] => []
  | .retarget q :: es => recordsMutable q es
  | _ :: es => p :: recordsMutable p es

/-- Retargeted between admission and settlement, one call's records disagree. -/
theorem mutable_records_disagree :
    recordsMutable .turn [.admit, .retarget .coding, .settle] = [.turn, .coding] := by
  simp [recordsMutable]

/-! ## A refused preparation -/

/-- A refused preparation is the owner phase `refused`: no event sequence
submits from it. -/
theorem refused_never_submits {T : Type} (es : List (NativeCallOwner.Event T)) :
    NativeCallOwner.submissions (NativeCallOwner.Phase.refused : NativeCallOwner.Phase T) es = 0 :=
  NativeCallOwner.settled_no_submissions (by simp [NativeCallOwner.Settled]) es

end Mettapedia.Protocols.Agents.NativeCallAnswers
