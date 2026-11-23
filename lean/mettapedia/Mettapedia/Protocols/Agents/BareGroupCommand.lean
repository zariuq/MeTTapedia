import Mettapedia.Protocols.Agents.ChannelAccess

/-!
# An operator's bare command in a group

In a group every bot reads the same message. A channel service therefore
takes `/command@bot` as a command only when the name is its own, and a bare
`/command` only in a private chat. A deployment whose operators mean a bare
command for every agent in the group declares it, and the rule becomes: a
bare command in a group is a command exactly when the declaration is present
and the sender is an operator (`bare_in_group_iff`).

Whatever the declaration says, no message of a sender who is not an operator
becomes a command (`command_only_from_operator`), and nothing but bare
commands in groups is decided differently (`declaration_changes_only_bare_in_group`);
without the declaration the rule is the earlier one (`undeclared_is_earlier_rule`).
The declaration only adds commands (`declaration_only_adds`).

A bare command is taken by every agent that declares it and lists the sender
(`bare_taken_by_every_declaring_agent`); an addressed one by at most the agent
it names (`addressed_taken_by_one`).

A message is either a command or ordinary input, never both (`routed_once`),
so what the service takes never reaches the agent's client as a question.
Before the declaration a client carried out an operator's bare command that
arrived as input; with it the service does, and for a new message the two
arrangements act on the same messages (`acts_as_before`). They differ on an
edit: the earlier client carried out an edited command again, and the service
takes only a new message (`edit_acted_before`, `edit_is_not_a_command`).

The launcher declares the access policy's owners as operators, so an owner's
bare command in a group is a command (`owner_bare_command`), and with no other
operator configured only an owner's is (`launcher_command_only_from_owner`).

Counterexamples: a rule that does not ask who sent the message lets anyone in
the group command the agent (`unguarded_rule_admits_stranger`); a rule that
takes every addressed command lets one bot act on another's
(`unaddressed_rule_takes_others`).

These are protocol-level statements about an abstract state, not a refinement
proof of the service.
-/

set_option autoImplicit false

namespace Mettapedia.Protocols.Agents.BareGroupCommand

open Mettapedia.Protocols.Agents

variable {Sender Bot : Type} [DecidableEq Sender] [DecidableEq Bot]

inductive Chat where
  | direct
  | group
  deriving DecidableEq, Repr

/-- A message as the service reads it. `addressee` is the bot a command names
(`/command@bot`), `none` for a bare one; `declared` says its first word is a
declared command; `fresh` that it is a new message, not an edit. -/
structure Message (Sender Bot : Type) where
  sender : Sender
  chat : Chat
  addressee : Option Bot
  declared : Bool
  fresh : Bool

/-- One agent's channel service. `known` is whether it has learned its own
username; until then it takes no addressed command. -/
structure Service (Sender Bot : Type) where
  operators : List Sender
  bot : Bot
  known : Bool
  bareInGroups : Bool

/-- Whether the command's form is one this service takes. -/
def addressed (svc : Service Sender Bot) (m : Message Sender Bot) : Bool :=
  match m.addressee, m.chat with
  | some b, _ => svc.known && decide (b = svc.bot)
  | none, .direct => true
  | none, .group => svc.bareInGroups

/-- The service's rule. -/
def isCommand (svc : Service Sender Bot) (m : Message Sender Bot) : Bool :=
  m.fresh && m.declared && svc.operators.contains m.sender && addressed svc m

/-- The rule before the declaration existed. -/
def earlierRule (svc : Service Sender Bot) (m : Message Sender Bot) : Bool :=
  m.fresh && m.declared && svc.operators.contains m.sender &&
    match m.addressee, m.chat with
    | some b, _ => svc.known && decide (b = svc.bot)
    | none, .direct => true
    | none, .group => false

def Message.bareInGroup (m : Message Sender Bot) : Bool :=
  m.addressee.isNone && decide (m.chat = .group)

theorem bare_in_group_iff (svc : Service Sender Bot) (m : Message Sender Bot)
    (hf : m.fresh = true) (hd : m.declared = true) (ha : m.addressee = none)
    (hg : m.chat = .group) :
    isCommand svc m = true ↔ svc.bareInGroups = true ∧ m.sender ∈ svc.operators := by
  simp [isCommand, addressed, hf, hd, ha, hg, and_comm]

theorem command_only_from_operator (svc : Service Sender Bot) (m : Message Sender Bot)
    (h : isCommand svc m = true) : m.sender ∈ svc.operators := by
  simp [isCommand] at h
  exact h.1.2

theorem command_is_declared_and_fresh (svc : Service Sender Bot) (m : Message Sender Bot)
    (h : isCommand svc m = true) : m.declared = true ∧ m.fresh = true := by
  simp [isCommand] at h
  exact ⟨h.1.1.2, h.1.1.1⟩

theorem undeclared_is_earlier_rule (svc : Service Sender Bot) (m : Message Sender Bot)
    (h : svc.bareInGroups = false) : isCommand svc m = earlierRule svc m := by
  cases m with
  | mk sender chat addressee declared fresh =>
    cases addressee <;> cases chat <;> simp [isCommand, earlierRule, addressed, h]

theorem declaration_changes_only_bare_in_group (svc : Service Sender Bot)
    (m : Message Sender Bot) (b : Bool) (h : m.bareInGroup = false) :
    isCommand { svc with bareInGroups := b } m = isCommand svc m := by
  cases m with
  | mk sender chat addressee declared fresh =>
    cases addressee <;> cases chat <;> simp_all [isCommand, addressed, Message.bareInGroup]

theorem declaration_only_adds (svc : Service Sender Bot) (m : Message Sender Bot)
    (h : isCommand { svc with bareInGroups := false } m = true) :
    isCommand { svc with bareInGroups := true } m = true := by
  cases m with
  | mk sender chat addressee declared fresh =>
    cases addressee <;> cases chat <;> simp_all [isCommand, addressed]

/-- Every agent in the group that declares it and lists the sender takes a
bare command: this is how an operator addresses them all at once. -/
theorem bare_taken_by_every_declaring_agent (svc : Service Sender Bot)
    (m : Message Sender Bot) (hf : m.fresh = true) (hd : m.declared = true)
    (ha : m.addressee = none) (hdecl : svc.bareInGroups = true)
    (hop : m.sender ∈ svc.operators) : isCommand svc m = true := by
  cases hc : m.chat <;> simp [isCommand, addressed, hf, hd, ha, hc, hdecl, hop]

theorem addressed_taken_by_one (a b : Service Sender Bot) (m : Message Sender Bot)
    (hne : a.bot ≠ b.bot) (name : Bot) (hn : m.addressee = some name)
    (ha : isCommand a m = true) : isCommand b m = false := by
  simp [isCommand, addressed, hn] at ha ⊢
  intro _ _ _ _ hb
  exact hne (ha.2.2.symm.trans hb)

/-! ## One route for each message -/

inductive Route where
  | command
  | input
  deriving DecidableEq, Repr

def route (svc : Service Sender Bot) (m : Message Sender Bot) : Route :=
  if isCommand svc m then .command else .input

theorem routed_once (svc : Service Sender Bot) (m : Message Sender Bot) :
    (route svc m = .command ↔ isCommand svc m = true) ∧
      (route svc m = .input ↔ isCommand svc m = false) := by
  unfold route
  cases isCommand svc m <;> simp

/-- The earlier client: an operator's declared bare command that arrived as
input was carried out there. It did not ask whether the message was new. -/
def earlierClientActs (svc : Service Sender Bot) (m : Message Sender Bot) : Bool :=
  !earlierRule svc m && m.declared && svc.operators.contains m.sender && m.addressee.isNone

/-- The earlier arrangement: the service's commands and the client's. -/
def earlierActs (svc : Service Sender Bot) (m : Message Sender Bot) : Bool :=
  earlierRule svc m || earlierClientActs svc m

theorem acts_as_before (svc : Service Sender Bot) (m : Message Sender Bot)
    (hdecl : svc.bareInGroups = true) (hf : m.fresh = true) (ha : m.addressee = none) :
    isCommand svc m = earlierActs svc m := by
  cases m with
  | mk sender chat addressee declared fresh =>
    simp only at hf ha
    subst hf ha
    cases chat <;> cases declared <;>
      simp [isCommand, addressed, earlierActs, earlierRule, earlierClientActs, hdecl]

theorem edit_is_not_a_command (svc : Service Sender Bot) (m : Message Sender Bot)
    (h : m.fresh = false) : isCommand svc m = false := by
  simp [isCommand, h]

theorem edit_acted_before (svc : Service Sender Bot) (m : Message Sender Bot)
    (hf : m.fresh = false) (hd : m.declared = true) (ha : m.addressee = none)
    (hop : m.sender ∈ svc.operators) : earlierActs svc m = true := by
  simp [earlierActs, earlierRule, earlierClientActs, hf, hd, ha, hop]

/-! ## Operators are the access policy's owners -/

section Policy

variable {Channel Name : Type}

/-- What the launcher declares to the service: the configured operators and
the access policy's owners. -/
def launched (configured : List Sender) (st : ChannelAccess.State Channel Sender Name)
    (bot : Bot) (known bare : Bool) : Service Sender Bot :=
  ⟨configured ++ st.owners, bot, known, bare⟩

theorem owner_bare_command (configured : List Sender)
    (st : ChannelAccess.State Channel Sender Name) (bot : Bot) (known : Bool)
    (m : Message Sender Bot) (hf : m.fresh = true) (hd : m.declared = true)
    (ha : m.addressee = none) (ho : ChannelAccess.mayCommand st m.sender = true) :
    isCommand (launched configured st bot known true) m = true := by
  apply bare_taken_by_every_declaring_agent _ _ hf hd ha rfl
  simp [launched]
  right
  simpa [ChannelAccess.mayCommand] using ho

theorem launcher_command_only_from_owner (st : ChannelAccess.State Channel Sender Name)
    (bot : Bot) (known bare : Bool) (m : Message Sender Bot)
    (h : isCommand (launched [] st bot known bare) m = true) :
    ChannelAccess.mayCommand st m.sender = true := by
  have := command_only_from_operator _ _ h
  simpa [launched, ChannelAccess.mayCommand] using this

end Policy

/-! ## Counterexamples -/

/-- A rule that takes a bare command in a group without asking who sent it. -/
def unguardedRule (svc : Service Sender Bot) (m : Message Sender Bot) : Bool :=
  m.fresh && m.declared && addressed svc m

/-- A rule that takes every addressed command, whoever it names. -/
def unaddressedRule (svc : Service Sender Bot) (m : Message Sender Bot) : Bool :=
  m.fresh && m.declared && svc.operators.contains m.sender

/-- Operator 7; this agent's bot is 1, the other agent's is 2. -/
def lila : Service Nat Nat := ⟨[7], 1, true, true⟩

def strangerStop : Message Nat Nat := ⟨5, .group, none, true, true⟩

def stopForGodel : Message Nat Nat := ⟨7, .group, some 2, true, true⟩

theorem unguarded_rule_admits_stranger :
    unguardedRule lila strangerStop = true ∧ isCommand lila strangerStop = false := by
  decide

theorem unaddressed_rule_takes_others :
    unaddressedRule lila stopForGodel = true ∧ isCommand lila stopForGodel = false := by
  decide

end Mettapedia.Protocols.Agents.BareGroupCommand
