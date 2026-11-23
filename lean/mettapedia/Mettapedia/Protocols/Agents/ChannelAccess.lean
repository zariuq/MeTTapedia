/-!
# Channel access: one policy for every chat channel

An agent is reached through chat channels (Telegram, Slack, Signal, IRC,
Mattermost, its console), each naming its senders and groups in its own way;
the policy is the same for all of them.

A message is decided on two independent axes: its visibility (drop it, or
record it into the agent's history) and its wake (never, on a mention, or
always; a direct message counts as a mention). A rule sets both, and may also
select how a wake works: a wake reason makes it a sender wake, which wakes the
agent at once with its whole banked budget, and an arming tier sets the fuel
the wake grants. Rules are set per sender class: an owner, a named group of
senders that carries its own rule, a listed sender, or a stranger. A sender is
listed when the generic allowlist or the channel's own allowlist names the
sender, directly or through a named group; the two lists combine. A scope's
access sits above the rules: the allowlist (the default) applies them, open
treats a stranger as listed, and disabled drops every message. Settings come
in layers (generic, channel, account, and for a group message the group), each
changing only the fields it states; a layer's named-group rules come before
the ones it inherits.

A recorded message carries its sender's class as provenance, and whether the
sender is trusted: an owner or a listed sender is, anyone else is not. The
label is something the agent reads with the message, never a block.

Admission is one protocol with two entry modes. A request: with requests on
(off by default), a stranger's direct message also asks to be added; requests
are capped per channel (three by default) and expire (a day by default), and
an optional acknowledgement (off by default) answers each such message with
the same text, whatever became of the request. An invite: the owner issues a
token with an expiry and a use count, and its holder redeems it in a message of
their own. Either way the sender ends up listed on the channel, or in the named
groups the owner chose. Only owner actions grant access: an approval from the
owner's control channel or command line, or the redemption of a token the owner
issued, within its expiry and use count. No message text and no action of the
agent does.

Proved here:

* a message wakes the agent only when it is recorded (`wake_recorded`);
* under the defaults no stranger's message is recorded, wakes the agent or is
  answered, and no message changes the state (`defaults_drop_strangers`,
  `defaults_keep_state`);
* the allowlists combine (`listed_combines`), open treats a stranger as listed
  (`open_stranger_as_listed`), and a recorded stranger's message is labelled
  untrusted (`stranger_untrusted`);
* only owner actions grant access: a change to the allowlists or named groups
  comes from an owner's approval or from redeeming a token that was live
  (`only_owner_grants`); every token comes from an owner and only loses uses
  (`tokens_from_owner`); a redemption spends exactly one use
  (`redeem_spends_one_use`); an approval lists the requester (`admit_lists`) and
  no one else (`admit_lists_only_requester`); no event makes an owner
  (`run_keeps_owners`), and only owners may command (`mayCommand_iff_owner`);
* requests stay within each channel's cap after every event, and so after
  every run (`run_within_cap`, `runAll_within_cap`);
* non-interference: what becomes of a message depends on the state only
  through its sender's class and trust (`outcome_by_class`), so for a stranger
  or a requester it is the same in any two states, whatever their named groups
  and membership (`stranger_outcome_ignores_groups`);
* a layer changes only the fields it states, and its named-group rules come
  first (`inherit_nothing`, `inherit_unstated`, `inherit_stated`).

The rewrites of `metta/gslt/module/godelclaw/AccessPolicy.module` are
`classify`, `Settings.rule`, `Rule.wakes`, the label and `inherit` here. These
are protocol-level statements about an abstract state, not a refinement proof
of the runtime.
-/

set_option autoImplicit false

namespace Mettapedia.Protocols.Agents.ChannelAccess

/-! ## Rules -/

/-- Whether a message enters the agent's history. -/
inductive Visibility where
  | drop | record
  deriving DecidableEq, Repr

/-- When a recorded message wakes the agent. -/
inductive Wake where
  | never | onMention | always
  deriving DecidableEq, Repr

/-- Both axes, and how a wake works: a `reason` makes it a sender wake, and a
`tier` sets the fuel it grants (none keeps the sender's own). -/
structure Rule where
  visibility : Visibility
  wake : Wake
  reason : Option String := none
  tier : Option String := none
  deriving DecidableEq, Repr

def Rule.dropped : Rule := ⟨.drop, .never, none, none⟩

/-- Whether a message under this rule wakes the agent. -/
def Rule.wakes (r : Rule) (mentioned : Bool) : Bool :=
  match r.visibility, r.wake with
  | .drop, _ => false
  | .record, .never => false
  | .record, .onMention => mentioned
  | .record, .always => true

/-- A named group's class carries the group's rule. -/
inductive SenderClass (Name : Type) where
  | owner
  | named (n : Name) (r : Rule)
  | listed
  | stranger
  deriving DecidableEq, Repr

def SenderClass.isStranger {Name : Type} : SenderClass Name → Bool
  | .stranger => true
  | _ => false

structure Rules (Name : Type) where
  owner : Rule
  listed : Rule
  stranger : Rule
  /-- Named groups' rules, in order: a sender in several takes the first. -/
  named : List (Name × Rule)

inductive Access where
  | disabled | allowlist | «open»
  deriving DecidableEq, Repr

structure Settings (Name : Type) where
  access : Access
  rules : Rules Name

variable {Channel Sender Group Name : Type}

/-- The rule a scope applies to a sender of a class. -/
def Settings.rule (cfg : Settings Name) (k : SenderClass Name) : Rule :=
  match cfg.access, k with
  | .disabled, _ => .dropped
  | _, .owner => cfg.rules.owner
  | _, .named _ r => r
  | _, .listed => cfg.rules.listed
  | .allowlist, .stranger => cfg.rules.stranger
  | .«open», .stranger => cfg.rules.listed

/-- Direct messages by default: owners and listed senders are recorded and
wake the agent; strangers are dropped. -/
def Settings.direct : Settings Name :=
  ⟨.allowlist, ⟨⟨.record, .always, none, none⟩, ⟨.record, .always, none, none⟩, .dropped, []⟩⟩

/-- Group messages by default: the same, except that a listed sender wakes the
agent by a mention. -/
def Settings.group : Settings Name :=
  ⟨.allowlist, ⟨⟨.record, .always, none, none⟩, ⟨.record, .onMention, none, none⟩, .dropped, []⟩⟩

theorem open_stranger_as_listed (cfg : Settings Name) (h : cfg.access = .«open») :
    cfg.rule .stranger = cfg.rule .listed := by
  simp [Settings.rule, h]

/-- One layer of settings: each field it states replaces the one beneath, and
its named-group rules come before the ones beneath. -/
structure Override (Name : Type) where
  access : Option Access := none
  owner : Option Rule := none
  listed : Option Rule := none
  stranger : Option Rule := none
  named : List (Name × Rule) := []

def inherit (outer : Settings Name) (layer : Override Name) : Settings Name :=
  ⟨layer.access.getD outer.access,
   ⟨layer.owner.getD outer.rules.owner, layer.listed.getD outer.rules.listed,
    layer.stranger.getD outer.rules.stranger, layer.named ++ outer.rules.named⟩⟩

/-- Settings through their layers, outermost first: generic, channel, account,
and for a group message the group. -/
def resolve (base : Settings Name) (layers : List (Override Name)) : Settings Name :=
  layers.foldl inherit base

theorem inherit_nothing (outer : Settings Name) : inherit outer {} = outer := by
  rcases outer with ⟨a, ⟨o, l, s, n⟩⟩
  simp [inherit]

theorem inherit_unstated (outer : Settings Name) (layer : Override Name) :
    (layer.access = none → (inherit outer layer).access = outer.access) ∧
    (layer.owner = none → (inherit outer layer).rules.owner = outer.rules.owner) ∧
    (layer.listed = none → (inherit outer layer).rules.listed = outer.rules.listed) ∧
    (layer.stranger = none → (inherit outer layer).rules.stranger = outer.rules.stranger) ∧
    (layer.named = [] → (inherit outer layer).rules.named = outer.rules.named) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> intro h <;> simp [inherit, h]

theorem inherit_stated (outer : Settings Name) (layer : Override Name) :
    (∀ a, layer.access = some a → (inherit outer layer).access = a) ∧
    (∀ r, layer.owner = some r → (inherit outer layer).rules.owner = r) ∧
    (∀ r, layer.listed = some r → (inherit outer layer).rules.listed = r) ∧
    (∀ r, layer.stranger = some r → (inherit outer layer).rules.stranger = r) ∧
    (inherit outer layer).rules.named = layer.named ++ outer.rules.named := by
  refine ⟨?_, ?_, ?_, ?_, rfl⟩ <;> intro v h <;> simp [inherit, h]

/-! ## Senders and their classes -/

/-- An allowlist entry: a sender, or a named group of senders. -/
inductive Entry (Sender Name : Type) where
  | sender (s : Sender)
  | named (n : Name)
  deriving DecidableEq, Repr

/-- A request to be added, kept for the owner. Its text is data: the owner
sees it quoted, and it decides nothing. -/
structure Request (Channel Sender : Type) where
  channel : Channel
  sender : Sender
  since : Nat
  text : String

/-- An invite: whoever presents `code` on `channel` before `expires`, while
uses remain, is placed as `into` says (the channel's allowlist when empty). -/
structure Token (Channel Name : Type) where
  code : String
  channel : Channel
  into : List Name
  expires : Nat
  uses : Nat

structure State (Channel Sender Name : Type) where
  /-- The generic allowlist, which holds on every channel. -/
  everywhere : List (Entry Sender Name)
  /-- Each channel's own allowlist. -/
  perChannel : Channel → List (Entry Sender Name)
  members : Name → List Sender
  owners : List Sender
  requests : List (Request Channel Sender)
  tokens : List (Token Channel Name)

variable [DecidableEq Sender]

def Entry.lists (members : Name → List Sender) (s : Sender) : Entry Sender Name → Bool
  | .sender t => decide (t = s)
  | .named n => (members n).contains s

/-- Whether a channel's allowlists, the generic one and its own, list a sender. -/
def listed (st : State Channel Sender Name) (c : Channel) (s : Sender) : Bool :=
  (st.everywhere ++ st.perChannel c).any (Entry.lists st.members s)

/-- Owners and listed senders are trusted; anyone else is not. -/
def trusted (st : State Channel Sender Name) (c : Channel) (s : Sender) : Bool :=
  st.owners.contains s || listed st c s

/-- An owner first; then the first named group with a rule that holds the
sender; then listed or a stranger. -/
def classify (cfg : Settings Name) (st : State Channel Sender Name) (c : Channel)
    (s : Sender) : SenderClass Name :=
  if st.owners.contains s then .owner
  else match cfg.rules.named.find? (fun p => (st.members p.1).contains s) with
    | some (n, r) => .named n r
    | none => if listed st c s then .listed else .stranger

def mayCommand (st : State Channel Sender Name) (s : Sender) : Bool := st.owners.contains s

theorem listed_combines (st : State Channel Sender Name) (c : Channel) (s : Sender) :
    listed st c s = (st.everywhere.any (Entry.lists st.members s) ||
      (st.perChannel c).any (Entry.lists st.members s)) := by
  simp [listed, List.any_append]

theorem mayCommand_iff_owner (cfg : Settings Name) (st : State Channel Sender Name)
    (c : Channel) (s : Sender) :
    mayCommand st s = true ↔ classify cfg st c s = .owner := by
  unfold mayCommand classify
  split
  · simp_all
  · split
    · simp_all
    · split <;> simp_all

theorem stranger_not_trusted (cfg : Settings Name) (st : State Channel Sender Name)
    (c : Channel) (s : Sender) (h : classify cfg st c s = .stranger) :
    trusted st c s = false := by
  unfold classify at h
  unfold trusted
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · simp_all

/-! ## Messages -/

structure Message (Channel Sender Group : Type) where
  channel : Channel
  /-- `none` for a direct message. -/
  group : Option Group
  sender : Sender
  mentioned : Bool
  text : String

/-- Provenance of a recorded message. -/
structure Label (Name : Type) where
  trusted : Bool
  sender : SenderClass Name
  deriving DecidableEq, Repr

structure Outcome (Name : Type) where
  /-- `none` when the message is dropped. -/
  recorded : Option (Label Name)
  wakes : Bool
  /-- The wake reason, when the message wakes the agent. -/
  reason : Option String
  /-- The arming tier, when the message is recorded. -/
  tier : Option String
  /-- Whether the access layer answers the sender. -/
  acknowledged : Bool
  deriving DecidableEq, Repr

/-- Admission by request, per channel or account. -/
structure Admission where
  requests : Bool := false
  cap : Nat := 3
  /-- Seconds a request stays pending. -/
  expiry : Nat := 86400
  acknowledge : Bool := false

/-- Resolved settings: for each channel or account its direct messages, its
groups, and its admission. -/
structure Config (Channel Group Name : Type) where
  direct : Channel → Settings Name
  group : Channel → Group → Settings Name
  admission : Channel → Admission

def Config.defaults : Config Channel Group Name :=
  ⟨fun _ => .direct, fun _ _ => .group, fun _ => {}⟩

def Config.settings (cfg : Config Channel Group Name) (m : Message Channel Sender Group) :
    Settings Name :=
  match m.group with
  | none => cfg.direct m.channel
  | some g => cfg.group m.channel g

/-- A stranger's direct message under the allowlist, with requests on, asks
to be added. -/
def asks (cfg : Config Channel Group Name) (st : State Channel Sender Name)
    (m : Message Channel Sender Group) : Bool :=
  m.group.isNone && (cfg.admission m.channel).requests &&
    decide ((cfg.direct m.channel).access = .allowlist) &&
    (classify (cfg.direct m.channel) st m.channel m.sender).isStranger

def outcome (cfg : Config Channel Group Name) (st : State Channel Sender Name)
    (m : Message Channel Sender Group) : Outcome Name :=
  let set := cfg.settings m
  let k := classify set st m.channel m.sender
  let r := set.rule k
  let w := r.wakes (m.group.isNone || m.mentioned)
  ⟨if r.visibility = .record then some ⟨trusted st m.channel m.sender, k⟩ else none,
   w,
   if w then r.reason else none,
   if r.visibility = .record then r.tier else none,
   asks cfg st m && (cfg.admission m.channel).acknowledge⟩

theorem Rule.wakes_recorded (r : Rule) (b : Bool) (h : r.wakes b = true) :
    r.visibility = .record := by
  rcases r with ⟨v, w, _, _⟩
  cases v <;> cases w <;> simp_all [Rule.wakes]

theorem wake_recorded (cfg : Config Channel Group Name) (st : State Channel Sender Name)
    (m : Message Channel Sender Group) (h : (outcome cfg st m).wakes = true) :
    (outcome cfg st m).recorded.isSome = true := by
  simp only [outcome] at h ⊢
  simp [Rule.wakes_recorded _ _ h]

theorem defaults_drop_strangers (st : State Channel Sender Name)
    (m : Message Channel Sender Group)
    (h : classify ((Config.defaults : Config Channel Group Name).settings m) st m.channel m.sender
      = .stranger) :
    outcome (Config.defaults : Config Channel Group Name) st m = ⟨none, false, none, none, false⟩ := by
  unfold outcome
  simp only [h]
  cases hg : m.group <;>
    simp [hg, Config.settings, Config.defaults, Settings.rule, Settings.direct, Settings.group,
      Rule.dropped, Rule.wakes, asks]

theorem stranger_untrusted (cfg : Config Channel Group Name) (st : State Channel Sender Name)
    (m : Message Channel Sender Group) (l : Label Name)
    (h : classify (cfg.settings m) st m.channel m.sender = .stranger)
    (hr : (outcome cfg st m).recorded = some l) :
    l = ⟨false, .stranger⟩ := by
  have ht := stranger_not_trusted _ _ _ _ h
  simp only [outcome, h, ht] at hr
  split at hr <;> simp_all

/-- What becomes of a message depends on the state only through its sender's
class and trust. -/
theorem outcome_by_class (cfg : Config Channel Group Name) (st₁ st₂ : State Channel Sender Name)
    (m : Message Channel Sender Group)
    (hk : classify (cfg.settings m) st₁ m.channel m.sender =
      classify (cfg.settings m) st₂ m.channel m.sender)
    (ht : trusted st₁ m.channel m.sender = trusted st₂ m.channel m.sender) :
    outcome cfg st₁ m = outcome cfg st₂ m := by
  have ha : asks cfg st₁ m = asks cfg st₂ m := by
    unfold asks
    cases hg : m.group with
    | none =>
      have hs : cfg.settings m = cfg.direct m.channel := by simp [Config.settings, hg]
      rw [hs] at hk
      rw [hk]
    | some g => simp
  simp only [outcome, hk, ht, ha]

/-- Non-interference. Whether a stranger's or a requester's message is
recorded, how it is labelled, whether it wakes the agent and whether the access
layer answers it are the same in any two states where the sender is a
stranger, so named groups and their membership cannot reach it. -/
theorem stranger_outcome_ignores_groups (cfg : Config Channel Group Name)
    (st₁ st₂ : State Channel Sender Name) (m : Message Channel Sender Group)
    (h₁ : classify (cfg.settings m) st₁ m.channel m.sender = .stranger)
    (h₂ : classify (cfg.settings m) st₂ m.channel m.sender = .stranger) :
    outcome cfg st₁ m = outcome cfg st₂ m :=
  outcome_by_class cfg st₁ st₂ m (h₁.trans h₂.symm)
    ((stranger_not_trusted _ _ _ _ h₁).trans (stranger_not_trusted _ _ _ _ h₂).symm)

/-! ## Admission -/

/-- Where an action comes from. `control` is the owner's control channel or
command line; `chat` is a sender's own message; the agent's tools are `agent`. -/
inductive Origin where
  | control | chat | agent
  deriving DecidableEq, Repr

inductive Event (Channel Sender Group Name : Type) where
  | message (m : Message Channel Sender Group)
  | redeem (origin : Origin) (c : Channel) (s : Sender) (code : String)
  | approve (origin : Origin) (c : Channel) (s : Sender) (into : List Name)
  | deny (origin : Origin) (c : Channel) (s : Sender)
  | issue (origin : Origin) (t : Token Channel Name)
  | revoke (origin : Origin) (code : String)

variable [DecidableEq Channel] [DecidableEq Name]

def requestsOn (st : State Channel Sender Name) (c : Channel) : List (Request Channel Sender) :=
  st.requests.filter (fun r => decide (r.channel = c))

/-- Forget expired requests, then keep this one unless its sender already has
one or the channel is at its cap. -/
def openRequest (cfg : Config Channel Group Name) (now : Nat) (st : State Channel Sender Name)
    (m : Message Channel Sender Group) : State Channel Sender Name :=
  let live := st.requests.filter (fun r => decide (now < r.since + (cfg.admission r.channel).expiry))
  let here := live.filter (fun r => decide (r.channel = m.channel))
  if here.any (fun r => decide (r.sender = m.sender)) || decide ((cfg.admission m.channel).cap ≤ here.length)
  then { st with requests := live }
  else { st with requests := ⟨m.channel, m.sender, now, m.text⟩ :: live }

def withdraw (st : State Channel Sender Name) (c : Channel) (s : Sender) :
    State Channel Sender Name :=
  { st with requests := st.requests.filter (fun r => !(decide (r.channel = c) && decide (r.sender = s))) }

/-- Admit a sender: list them on the channel, or, when groups are named, place
them into those groups; any request of theirs there is settled. -/
def admit (st : State Channel Sender Name) (c : Channel) (s : Sender) (into : List Name) :
    State Channel Sender Name :=
  let w := withdraw st c s
  if into.isEmpty then
    { w with perChannel := fun d => if d = c then .sender s :: w.perChannel d else w.perChannel d }
  else
    { w with members := fun n => if n ∈ into then s :: w.members n else w.members n }

/-- Whether a token admits through `code` on channel `c` at time `now`. -/
def Token.live (now : Nat) (c : Channel) (code : String) (t : Token Channel Name) : Bool :=
  decide (t.code = code) && decide (t.channel = c) && decide (now < t.expires) && decide (0 < t.uses)

/-- Spend one use of the first token that satisfies `p`; a token whose last use
is spent is gone. -/
def spend (p : Token Channel Name → Bool) :
    List (Token Channel Name) → Option (Token Channel Name × List (Token Channel Name))
  | [] => none
  | t :: ts =>
    if p t then some (t, if t.uses ≤ 1 then ts else { t with uses := t.uses - 1 } :: ts)
    else (spend p ts).map (fun x => (x.1, t :: x.2))

def usesLeft : List (Token Channel Name) → Nat
  | [] => 0
  | t :: ts => t.uses + usesLeft ts

def run (cfg : Config Channel Group Name) (now : Nat) (st : State Channel Sender Name) :
    Event Channel Sender Group Name → State Channel Sender Name
  | .message m => if asks cfg st m then openRequest cfg now st m else st
  | .redeem .chat c s code =>
    match spend (Token.live now c code) st.tokens with
    | some (t, rest) => { admit st c s t.into with tokens := rest }
    | none => st
  | .approve .control c s into => admit st c s into
  | .deny .control c s => withdraw st c s
  | .issue .control t => { st with tokens := t :: st.tokens }
  | .revoke .control code => { st with tokens := st.tokens.filter (fun t => !decide (t.code = code)) }
  | _ => st

def runAll (cfg : Config Channel Group Name) :
    State Channel Sender Name → List (Nat × Event Channel Sender Group Name) → State Channel Sender Name
  | st, [] => st
  | st, (now, e) :: rest => runAll cfg (run cfg now st e) rest

theorem defaults_keep_state (now : Nat) (st : State Channel Sender Name)
    (m : Message Channel Sender Group) :
    run (Config.defaults : Config Channel Group Name) now st (.message m) = st := by
  simp [run, asks, Config.defaults]

omit [DecidableEq Sender] [DecidableEq Channel] [DecidableEq Name] in
theorem spend_some {p : Token Channel Name → Bool} :
    ∀ {l : List (Token Channel Name)} {t : Token Channel Name} {rest : List (Token Channel Name)},
      spend p l = some (t, rest) → t ∈ l ∧ p t = true
  | [], _, _, h => by simp [spend] at h
  | u :: us, t, rest, h => by
    unfold spend at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      exact ⟨List.mem_cons_self .., by assumption⟩
    · cases hs : spend p us with
      | none => simp [hs] at h
      | some x =>
        simp only [hs, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h
        have := spend_some hs
        exact ⟨List.mem_cons_of_mem _ this.1, this.2⟩

omit [DecidableEq Sender] [DecidableEq Channel] [DecidableEq Name] in
theorem spend_uses {p : Token Channel Name → Bool} (hp : ∀ u, p u = true → 0 < u.uses) :
    ∀ {l : List (Token Channel Name)} {t : Token Channel Name} {rest : List (Token Channel Name)},
      spend p l = some (t, rest) → usesLeft rest + 1 = usesLeft l
  | [], _, _, h => by simp [spend] at h
  | u :: us, t, rest, h => by
    unfold spend at h
    split at h
    · rename_i hu
      have pos := hp u hu
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      split <;> simp only [usesLeft] <;> omega
    · cases hs : spend p us with
      | none => simp [hs] at h
      | some x =>
        simp only [hs, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have := spend_uses hp hs
        simp only [usesLeft]
        omega

omit [DecidableEq Sender] [DecidableEq Channel] [DecidableEq Name] in
theorem spend_tokens {p : Token Channel Name → Bool} :
    ∀ {l : List (Token Channel Name)} {t u : Token Channel Name} {rest : List (Token Channel Name)},
      spend p l = some (u, rest) → t ∈ rest → t ∈ l ∨ (u ∈ l ∧ t = { u with uses := u.uses - 1 })
  | [], _, _, _, h, _ => by simp [spend] at h
  | v :: vs, t, u, rest, h, ht => by
    unfold spend at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      split at ht
      · exact .inl (List.mem_cons_of_mem _ ht)
      · rcases List.mem_cons.mp ht with rfl | ht
        · exact .inr ⟨List.mem_cons_self .., rfl⟩
        · exact .inl (List.mem_cons_of_mem _ ht)
    · cases hs : spend p vs with
      | none => simp [hs] at h
      | some x =>
        simp only [hs, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        rcases List.mem_cons.mp ht with rfl | ht
        · exact .inl (List.mem_cons_self ..)
        · rcases spend_tokens hs ht with h' | ⟨h', e⟩
          · exact .inl (List.mem_cons_of_mem _ h')
          · exact .inr ⟨List.mem_cons_of_mem _ h', e⟩

/-- Only owner actions grant access: any change to the allowlists or the named
groups comes from an approval through the owner's control channel, or from a
sender's own redemption of a token that was live: its code and channel match,
it had not expired, and it had a use left. -/
theorem only_owner_grants (cfg : Config Channel Group Name) (now : Nat)
    (st : State Channel Sender Name) (e : Event Channel Sender Group Name)
    (h : (run cfg now st e).everywhere ≠ st.everywhere ∨
      (run cfg now st e).perChannel ≠ st.perChannel ∨
      (run cfg now st e).members ≠ st.members) :
    (∃ c s into, e = .approve .control c s into) ∨
    (∃ c s code, e = .redeem .chat c s code ∧
      ∃ t ∈ st.tokens, t.code = code ∧ t.channel = c ∧ now < t.expires ∧ 0 < t.uses) := by
  cases e with
  | message m =>
    exfalso
    simp only [run] at h
    split at h
    · simp only [openRequest] at h; split at h <;> simp at h
    · simp at h
  | redeem o c s code =>
    cases o with
    | chat =>
      simp only [run] at h
      cases hs : spend (Token.live now c code) st.tokens with
      | none => simp [hs] at h
      | some x =>
        rcases x with ⟨t, rest⟩
        obtain ⟨mem, live⟩ := spend_some hs
        simp only [Token.live, Bool.and_eq_true, decide_eq_true_eq] at live
        exact .inr ⟨c, s, code, rfl, t, mem, live.1.1.1, live.1.1.2, live.1.2, live.2⟩
    | control => simp [run] at h
    | agent => simp [run] at h
  | approve o c s into =>
    cases o with
    | control => exact .inl ⟨c, s, into, rfl⟩
    | chat => simp [run] at h
    | agent => simp [run] at h
  | deny o c s => cases o <;> simp [run, withdraw] at h
  | issue o t => cases o <;> simp [run] at h
  | revoke o code => cases o <;> simp [run] at h

/-- Every token comes from an owner: one in the state after an event is the
one an owner just issued, or a token that was there before, with the same
code, channel, placement and expiry and no more uses. -/
theorem tokens_from_owner (cfg : Config Channel Group Name) (now : Nat)
    (st : State Channel Sender Name) (e : Event Channel Sender Group Name)
    (t : Token Channel Name) (ht : t ∈ (run cfg now st e).tokens) :
    e = .issue .control t ∨
    ∃ u ∈ st.tokens, u.code = t.code ∧ u.channel = t.channel ∧ u.into = t.into ∧
      u.expires = t.expires ∧ t.uses ≤ u.uses := by
  have same : t ∈ st.tokens → ∃ u ∈ st.tokens, u.code = t.code ∧ u.channel = t.channel ∧
      u.into = t.into ∧ u.expires = t.expires ∧ t.uses ≤ u.uses :=
    fun m => ⟨t, m, rfl, rfl, rfl, rfl, Nat.le_refl _⟩
  cases e with
  | message m =>
    simp only [run] at ht
    split at ht
    · simp only [openRequest] at ht; split at ht <;> exact .inr (same ht)
    · exact .inr (same ht)
  | redeem o c s code =>
    cases o with
    | chat =>
      simp only [run] at ht
      cases hs : spend (Token.live now c code) st.tokens with
      | none => simp only [hs] at ht; exact .inr (same ht)
      | some x =>
        rcases x with ⟨u, rest⟩
        simp only [hs] at ht
        rcases spend_tokens hs ht with m | ⟨m, rfl⟩
        · exact .inr (same m)
        · exact .inr ⟨u, m, rfl, rfl, rfl, rfl, Nat.sub_le _ _⟩
    | control => exact .inr (same ht)
    | agent => exact .inr (same ht)
  | approve o c s into =>
    cases o <;> simp only [run, admit, withdraw] at ht <;> (try split at ht) <;> exact .inr (same ht)
  | deny o c s => cases o <;> exact .inr (same ht)
  | issue o u =>
    cases o with
    | control =>
      rcases List.mem_cons.mp ht with rfl | m
      · exact .inl rfl
      · exact .inr (same m)
    | chat => exact .inr (same ht)
    | agent => exact .inr (same ht)
  | revoke o code =>
    cases o with
    | control => exact .inr (same (List.mem_filter.mp ht).1)
    | chat => exact .inr (same ht)
    | agent => exact .inr (same ht)

/-- A redemption that admits spends exactly one use of the token it used. -/
theorem redeem_spends_one_use (cfg : Config Channel Group Name) (now : Nat)
    (st : State Channel Sender Name) (c : Channel) (s : Sender) (code : String)
    (t : Token Channel Name) (rest : List (Token Channel Name))
    (h : spend (Token.live now c code) st.tokens = some (t, rest)) :
    (run cfg now st (.redeem .chat c s code)).tokens = rest ∧
      usesLeft rest + 1 = usesLeft st.tokens := by
  refine ⟨by simp [run, h], spend_uses ?_ h⟩
  intro u hu
  simp only [Token.live, Bool.and_eq_true, decide_eq_true_eq] at hu
  exact hu.2

theorem run_keeps_owners (cfg : Config Channel Group Name) (now : Nat)
    (st : State Channel Sender Name) (e : Event Channel Sender Group Name) :
    (run cfg now st e).owners = st.owners := by
  cases e with
  | message m =>
    simp only [run]
    split
    · simp only [openRequest]; split <;> rfl
    · rfl
  | redeem o c s code =>
    cases o
    · rfl
    · simp only [run]
      split
      · simp only [admit, withdraw]; split <;> rfl
      · rfl
    · rfl
  | approve o c s into =>
    cases o <;> simp only [run, admit, withdraw] <;> (try split) <;> rfl
  | deny o c s => cases o <;> rfl
  | issue o t => cases o <;> rfl
  | revoke o code => cases o <;> rfl

theorem admit_lists (st : State Channel Sender Name) (c : Channel) (s : Sender) :
    listed (admit st c s []) c s = true := by
  simp [admit, withdraw, listed, Entry.lists]

theorem admit_lists_only_requester (st : State Channel Sender Name) (c d : Channel)
    (s t : Sender) (into : List Name) (hts : t ≠ s) :
    listed (admit st c s into) d t = listed st d t := by
  unfold admit withdraw listed
  split
  · by_cases hd : d = c
    · simp [hd, Entry.lists, Ne.symm hts]
    · simp [hd]
  · simp only
    congr 1
    funext e
    cases e with
    | sender u => rfl
    | named n => by_cases hn : n ∈ into <;> simp [Entry.lists, hn, hts]

omit [DecidableEq Sender] [DecidableEq Name] in
/-- Filtering first never adds requests on a channel. -/
theorem requestsOn_filter_le (l : List (Request Channel Sender)) (c : Channel)
    (p : Request Channel Sender → Bool) :
    ((l.filter p).filter (fun r => decide (r.channel = c))).length ≤
      (l.filter (fun r => decide (r.channel = c))).length := by
  rw [List.filter_filter, show (fun r : Request Channel Sender => decide (r.channel = c) && p r) =
    (fun r => p r && decide (r.channel = c)) from funext fun r => Bool.and_comm _ _,
    ← List.filter_filter]
  exact List.length_filter_le _ _

theorem run_within_cap (cfg : Config Channel Group Name) (now : Nat)
    (st : State Channel Sender Name) (e : Event Channel Sender Group Name) (c : Channel)
    (h : (requestsOn st c).length ≤ (cfg.admission c).cap) :
    (requestsOn (run cfg now st e) c).length ≤ (cfg.admission c).cap := by
  have withdrawn : ∀ (d : Channel) (s : Sender),
      (requestsOn (withdraw st d s) c).length ≤ (cfg.admission c).cap :=
    fun d s => Nat.le_trans (requestsOn_filter_le _ c _) h
  cases e with
  | message m =>
    simp only [run]
    split
    · simp only [openRequest]
      split
      · exact Nat.le_trans (requestsOn_filter_le _ c _) h
      · rename_i full
        simp only [requestsOn, List.filter_cons]
        by_cases hc : m.channel = c
        · subst hc
          simp only [decide_true, ite_true, List.length_cons]
          simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, Nat.not_le] at full
          exact full.2
        · simp only [hc, decide_false]
          exact Nat.le_trans (requestsOn_filter_le _ c _) h
    · exact h
  | redeem o d s code =>
    cases o
    · exact h
    · simp only [run]
      split
      · simp only [admit]; split <;> exact withdrawn d s
      · exact h
    · exact h
  | approve o d s into =>
    cases o
    · simp only [run, admit]; split <;> exact withdrawn d s
    all_goals exact h
  | deny o d s =>
    cases o
    · exact withdrawn d s
    all_goals exact h
  | issue o t => cases o <;> exact h
  | revoke o code => cases o <;> exact h

theorem runAll_within_cap (cfg : Config Channel Group Name) (c : Channel) :
    ∀ (evs : List (Nat × Event Channel Sender Group Name)) (st : State Channel Sender Name),
      (requestsOn st c).length ≤ (cfg.admission c).cap →
      (requestsOn (runAll cfg st evs) c).length ≤ (cfg.admission c).cap
  | [], _, h => h
  | (now, e) :: rest, st, h => runAll_within_cap cfg c rest _ (run_within_cap cfg now st e c h)

end Mettapedia.Protocols.Agents.ChannelAccess
