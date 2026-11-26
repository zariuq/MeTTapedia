import Mettapedia.Languages.MeTTa.SpaceTheory.HeadSealing
import Mathlib.Data.Set.Insert

/-!
# Owner-checked writes to sealed MeTTa heads

A received packet contains an owner, a request key and an edit, not a
local capability. The authenticated peer is supplied by the transport,
outside the packet. The owner alone records grants, bound to the peer
and the exact edit. Delivery rechecks the offered facet and the
proposed before-space, and spends the request key with the edit.

Cancellation of a grant and stopping a brand are distinct owner
actions. Neither destroys a locally held value. The theorems are
conditional on peer authentication and on retaining the owner's state;
they do not specify cryptography or recovery from a lost receipt.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.SpaceTheory.HeadWriteProtocol

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.Seal (Brand Config Policy)
open HeadSealing (Registry Edit Spaces Allowed LocalWrite OffersWrite)

structure Owner (Instance : Type*) where
  identity : Nat
  seals : Registry Instance
  holdingsPolicy : Policy Atom

structure Grant (Instance : Type*) where
  peer : Nat
  offered : List Nat
  edit : Edit Instance

structure Packet (Instance : Type*) where
  owner : Nat
  key : Nat
  edit : Edit Instance

structure State (Instance : Type*) where
  spaces : Spaces Instance
  holdings : Config Atom
  grants : Nat → Option (Grant Instance) := fun _ => none
  cancelled : Set Nat := ∅
  stopped : Set Brand := ∅
  spent : List Nat := []

def Enabled {Instance : Type*} (owner : Owner Instance) (state : State Instance) (grant : Grant Instance) : Prop :=
  Allowed owner.seals state.holdings grant.peer grant.offered grant.edit ∧
    ∀ h brand, owner.seals.brand ⟨grant.edit.instanceId, h⟩ = some brand → grant.edit.touches h →
      brand ∉ state.stopped

def Ready {Instance : Type*} (owner : Owner Instance) (state : State Instance)
    (authenticatedPeer : Nat) (packet : Packet Instance) : Prop :=
  packet.owner = owner.identity ∧ packet.key ∉ state.cancelled ∧ packet.key ∉ state.spent ∧
    ∃ grant, state.grants packet.key = some grant ∧ grant.peer = authenticatedPeer ∧
      grant.edit = packet.edit ∧ Enabled owner state grant

/-- Only the last event is a network input. Grant and cancellation
events belong to the owner, as do changes of its local holdings. -/
inductive Event (Instance : Type*) where
  | issued (key : Nat) (grant : Grant Instance)
  | cancelled (key : Nat)
  | stopped (brand : Brand)
  | holdings
  | received (authenticatedPeer : Nat) (packet : Packet Instance)

inductive Step {Instance : Type*} [DecidableEq Instance] (owner : Owner Instance) :
    State Instance → Event Instance → State Instance → Prop where
  | issue {before : State Instance} {key : Nat} {grant : Grant Instance} :
      before.grants key = none → Enabled owner before grant →
      Step owner before (.issued key grant) {before with grants := Function.update before.grants key (some grant)}
  | cancel (before : State Instance) (key : Nat) :
      Step owner before (.cancelled key) {before with cancelled := insert key before.cancelled}
  | stop (before : State Instance) (brand : Brand) :
      Step owner before (.stopped brand) {before with stopped := insert brand before.stopped}
  | holdings {before : State Instance} {next : Config Atom} :
      Mettapedia.Languages.MeTTa.Seal.Step owner.holdingsPolicy before.holdings next →
      Step owner before .holdings {before with holdings := next}
  | deliver {before : State Instance} {authenticatedPeer : Nat} {packet : Packet Instance} :
      Ready owner before authenticatedPeer packet →
      before.spaces packet.edit.instanceId = packet.edit.expected →
      Step owner before (.received authenticatedPeer packet)
        {before with
          spaces := Function.update before.spaces packet.edit.instanceId packet.edit.replacement
          spent := packet.key :: before.spent}

section Delivery

variable {Instance : Type*} [DecidableEq Instance] {owner : Owner Instance}
variable {before after : State Instance} {peer : Nat} {packet : Packet Instance}

theorem received_refines_local (step : Step owner before (.received peer packet) after) :
    ∃ grant, before.grants packet.key = some grant ∧ grant.peer = peer ∧ grant.edit = packet.edit ∧
      LocalWrite owner.seals before.holdings peer grant.offered packet.edit before.spaces after.spaces := by
  cases step with
  | deliver ready fresh =>
    obtain ⟨_, _, _, grant, issued, sender, exactEdit, allowed, _⟩ := ready
    exact ⟨grant, issued, sender, exactEdit, by simpa only [sender, exactEdit] using allowed, fresh, rfl⟩

theorem wrong_owner_refused (different : packet.owner ≠ owner.identity) :
    ¬Step owner before (.received peer packet) after := by
  intro accepted
  cases accepted with
  | deliver ready _ => exact different ready.1

theorem unissued_packet_refused (unissued : before.grants packet.key = none) :
    ¬Step owner before (.received peer packet) after := by
  intro accepted
  obtain ⟨grant, recorded, _⟩ := received_refines_local accepted
  rw [unissued] at recorded
  cases recorded

theorem wrong_peer_refused {grant : Grant Instance} (listed : before.grants packet.key = some grant)
    (different : grant.peer ≠ peer) : ¬Step owner before (.received peer packet) after := by
  intro committed
  obtain ⟨used, issued, name, _⟩ := received_refines_local committed
  have same := Option.some.inj (listed.symm.trans issued)
  exact different (same.symm ▸ name)

theorem different_edit_refused {grant : Grant Instance} (listed : before.grants packet.key = some grant)
    (different : grant.edit ≠ packet.edit) : ¬Step owner before (.received peer packet) after := by
  intro committed
  obtain ⟨used, issued, _, promise, _⟩ := received_refines_local committed
  have same := Option.some.inj (listed.symm.trans issued)
  exact different (same.symm ▸ promise)

theorem stale_snapshot_refused (stale : before.spaces packet.edit.instanceId ≠ packet.edit.expected) :
    ¬Step owner before (.received peer packet) after := by
  intro accepted
  cases accepted with
  | deliver _ applies => exact stale applies

theorem cancellation_refused (cancelled : packet.key ∈ before.cancelled) :
    ¬Step owner before (.received peer packet) after := by
  intro accepted
  cases accepted with
  | deliver ready _ => exact ready.2.1 cancelled

theorem spent_refused (used : packet.key ∈ before.spent) : ¬Step owner before (.received peer packet) after := by
  intro accepted
  cases accepted with
  | deliver ready _ => exact ready.2.2.1 used

theorem stopped_brand_refused {head : String} {brand : Brand}
    (registered : owner.seals.brand ⟨packet.edit.instanceId, head⟩ = some brand)
    (touches : packet.edit.touches head) (stopped : brand ∈ before.stopped) :
    ¬Step owner before (.received peer packet) after := by
  intro accepted
  cases accepted with
  | deliver ready _ =>
    obtain ⟨_, _, _, grant, _, _, sameEdit, _, active⟩ := ready
    rw [sameEdit] at active
    exact active head brand registered touches stopped

theorem no_new_write_right_on_wire {address : HeadSealing.Address Instance} {brand : Brand}
    (sealed : owner.seals.brand address = some brand)
    (hasNone : ∀ offered, ¬OffersWrite before.holdings peer offered brand)
    (step : Step owner before (.received peer packet) after) :
    HeadSealing.projection address.head (before.spaces address.instanceId) =
      HeadSealing.projection address.head (after.spaces address.instanceId) := by
  obtain ⟨grant, _, _, _, localWrite⟩ := received_refines_local step
  exact HeadSealing.no_facet_keeps_projection sealed (hasNone grant.offered) localWrite

end Delivery

inductive History {Instance : Type*} [DecidableEq Instance] (owner : Owner Instance) :
    State Instance → List (Event Instance) → State Instance → Prop where
  | nil (state : State Instance) : History owner state [] state
  | cons {before middle after : State Instance} {event : Event Instance} {remaining : List (Event Instance)} :
      Step owner before event middle → History owner middle remaining after → History owner before (event :: remaining) after

section Histories

variable {Instance : Type*} [DecidableEq Instance] {owner : Owner Instance}
variable {initial final : State Instance} {event : Event Instance} {history : List (Event Instance)}

theorem grant_is_existing_or_issued {key : Nat} {grant : Grant Instance}
    (step : Step owner initial event final) (listed : final.grants key = some grant) :
    initial.grants key = some grant ∨ event = .issued key grant := by
  cases step with
  | @issue atKey offer absent allowed =>
    by_cases matched : key = atKey
    · subst key
      have same := Option.some.inj (by simpa only [Function.update_self] using listed)
      exact Or.inr (congrArg (Event.issued atKey) same)
    · exact Or.inl (by simpa only [Function.update_of_ne matched] using listed)
  | cancel | stop | holdings | deliver => exact Or.inl listed

theorem approved_in_history {key : Nat} {grant : Grant Instance}
    (path : History owner initial history final) (listed : final.grants key = some grant) :
    initial.grants key = some grant ∨ Event.issued key grant ∈ history := by
  induction path with
  | nil => exact Or.inl listed
  | cons step _ ih =>
    rcases ih listed with prior | inTail
    · rcases grant_is_existing_or_issued step prior with older | issued
      · exact Or.inl older
      · exact Or.inr (List.mem_cons.mpr (Or.inl issued.symm))
    · exact Or.inr (List.mem_cons_of_mem _ inTail)

/-- With an initially unissued key, every accepted delivery has an
actual earlier issuance to that peer for that edit. -/
theorem delivery_was_issued {peer : Nat} {packet : Packet Instance} {after : State Instance}
    (path : History owner initial history final) (newKey : initial.grants packet.key = none)
    (accepted : Step owner final (.received peer packet) after) :
    ∃ grant, Event.issued packet.key grant ∈ history ∧ grant.peer = peer ∧ grant.edit = packet.edit := by
  obtain ⟨grant, listed, peerEq, editEq, _⟩ := received_refines_local accepted
  rcases approved_in_history path listed with old | arrived
  · rw [newKey] at old
    cases old
  · exact ⟨grant, arrived, peerEq, editEq⟩

theorem earlier_brand_stop_persists (path : History owner initial history final)
    {brand : Brand} (stopped : brand ∈ initial.stopped) : brand ∈ final.stopped := by
  induction path with
  | nil => exact stopped
  | cons step _ ih =>
    apply ih
    cases step with
    | stop _ => exact Set.mem_insert_of_mem _ stopped
    | issue | cancel | holdings | deliver => exact stopped

theorem earlier_cancellation_persists (path : History owner initial history final)
    {key : Nat} (cancelled : key ∈ initial.cancelled) : key ∈ final.cancelled := by
  induction path with
  | nil => exact cancelled
  | cons step _ ih =>
    apply ih
    cases step with
    | cancel _ => exact Set.mem_insert_of_mem _ cancelled
    | issue | stop | holdings | deliver => exact cancelled

def receiptKey : Event Instance → Option Nat
  | .received _ packet => some packet.key
  | _ => none

theorem receipts_are_accepted_deliveries (path : History owner initial history final) :
    final.spent = (history.filterMap receiptKey).reverse ++ initial.spent := by
  induction path with
  | nil => rfl
  | cons step _ ih =>
    rw [ih]
    cases step <;> simp [List.filterMap_cons, receiptKey, List.append_assoc]

theorem accepted_keys_distinct (path : History owner initial history final) (distinct : initial.spent.Nodup) :
    final.spent.Nodup := by
  induction path with
  | nil => exact distinct
  | cons step _ ih =>
    apply ih
    cases step with
    | deliver ready _ => exact List.nodup_cons.mpr ⟨ready.2.2.1, distinct⟩
    | issue | cancel | stop | holdings => exact distinct

theorem never_two_deliveries_for_one_key (path : History owner initial history final)
    (distinct : initial.spent.Nodup) : (history.filterMap receiptKey).Nodup := by
  have accepted := accepted_keys_distinct path distinct
  rw [receipts_are_accepted_deliveries path, List.nodup_append] at accepted
  exact List.nodup_reverse.mp accepted.1

theorem holdings_follow_capability_steps (path : History owner initial history final) :
    Mettapedia.Languages.MeTTa.Seal.Reach owner.holdingsPolicy initial.holdings final.holdings := by
  induction path with
  | nil => exact .refl
  | cons step _ ih =>
    cases step with
    | holdings capabilityStep => exact .head capabilityStep ih
    | issue | cancel | stop | deliver => exact ih

/-- The protocol cannot create a right for an existing seal. If a delivery
changes it, an authority for that brand existed before the history's
ordinary capability steps. A grant is not a new capability constructor. -/
theorem delivery_has_capability_lineage
    {peer : Nat} {packet : Packet Instance} {after : State Instance} {brand : Brand} {head : String}
    (path : History owner initial history final) (existing : brand < initial.holdings.nextBrand)
    (sealed : owner.seals.brand ⟨packet.edit.instanceId, head⟩ = some brand) (changeHead : packet.edit.touches head)
    (landed : Step owner final (.received peer packet) after) :
    initial.holdings.anyCap brand Mettapedia.Languages.MeTTa.Seal.Rights.sealRight := by
  obtain ⟨grant, _, _, _, write⟩ := received_refines_local landed
  exact HeadSealing.successful_write_is_from_existing_authority
    (holdings_follow_capability_steps path) existing sealed changeHead write

end Histories

section Controls

open Mettapedia.Languages.MeTTa.Seal (Rights)

private def root : HeadSealing.Address Nat := ⟨0, "weather"⟩
private def host : Owner Nat := ⟨11, Registry.one root 9, fun principal _ _ => principal = 7⟩
private def authored : Atom := .expression [.symbol "=", .expression [.symbol "weather"], .symbol "warm"]
private def edit : Edit Nat := ⟨0, [], [], [authored], []⟩
private def grant : Grant Nat := ⟨7, [0], edit⟩
private def packet : Packet Nat := ⟨11, 5, edit⟩

private def starting : State Nat where
  spaces := fun _ => []
  holdings := ⟨fun peer => if peer = 7 then [.cap 9 Rights.sealOnly] else [], 10, 0⟩

private def booked : State Nat := {starting with grants := Function.update starting.grants 5 (some grant)}
private def landed : State Nat where
  spaces := Function.update booked.spaces 0 [authored]
  holdings := booked.holdings
  grants := booked.grants
  cancelled := booked.cancelled
  stopped := booked.stopped
  spent := [5]

private theorem initial_permission : Enabled host starting grant := by
  constructor
  · intro h brand issued _
    have same := (Registry.one_exact.mp issued).2
    obtain rfl := same
    exact ⟨0, List.mem_cons_self, Rights.sealOnly, rfl, rfl⟩
  · intro h brand issued touched included
    exact included

private theorem issuance : Step host starting (.issued 5 grant) booked :=
  .issue rfl initial_permission

private theorem actual_delivery : Step host booked (.received 7 packet) landed := by
  apply Step.deliver
  · refine ⟨rfl, fun absent => absent, List.not_mem_nil, grant, ?_, rfl, rfl, initial_permission⟩
    simp only [booked, packet, Function.update_self]
  · rfl

theorem delivery_commits_once :
    History host starting [.issued 5 grant, .received 7 packet] landed ∧
      landed.spaces 0 = [authored] ∧ landed.spent = [5] ∧
      ∀ after, ¬Step host landed (.received 7 packet) after :=
  ⟨.cons issuance (.cons actual_delivery (.nil _)), rfl, rfl,
    fun _ => spent_refused List.mem_cons_self⟩

theorem another_peer_or_owner_cannot_reuse_the_packet :
    (∀ after, ¬Step host booked (.received 8 packet) after) ∧
      (∀ after, ¬Step {host with identity := 12} booked (.received 7 packet) after) := by
  constructor
  · intro after
    apply wrong_peer_refused (grant := grant)
    · simp only [booked, packet, Function.update_self]
    · decide +kernel
  · intro after
    exact wrong_owner_refused (by decide +kernel)

theorem altering_the_recorded_edit_is_refused :
    let altered : Packet Nat := {packet with edit := {edit with inserted := [.symbol "other"]}}
    ∀ after, ¬Step host booked (.received 7 altered) after := by
  intro altered after
  apply different_edit_refused (grant := grant)
  · change Function.update starting.grants 5 (some grant) 5 = some grant
    simp only [Function.update_self]
  · decide +kernel

theorem stopping_a_facet_blocks_an_issued_write :
    let revoked : State Nat := {booked with stopped := insert 9 booked.stopped}
    Step host booked (.stopped 9) revoked ∧ ∀ after, ¬Step host revoked (.received 7 packet) after := by
  intro revoked
  refine ⟨.stop booked 9, fun after => stopped_brand_refused (head := "weather") (brand := 9) ?_ ?_ ?_⟩
  · rfl
  · exact ⟨authored, List.mem_cons_self, rfl⟩
  · exact Set.mem_insert _ _

private def parallel : State Nat := {booked with grants := Function.update booked.grants 6 (some grant)}
private def wroteFirst : State Nat := {landed with grants := parallel.grants}
private def delayed : Packet Nat := {packet with key := 6}

/-- A separate valid key cannot publish a patch for a space that has
since changed. This check is independent of replay by the same key. -/
theorem competing_grant_is_stale_after_delivery :
    History host booked [.issued 6 grant, .received 7 packet] wroteFirst ∧
      Ready host wroteFirst 7 delayed ∧ ∀ after, ¬Step host wroteFirst (.received 7 delayed) after := by
  have second : Step host booked (.issued 6 grant) parallel := .issue rfl initial_permission
  have firstReady : Ready host parallel 7 packet := by
    refine ⟨rfl, fun absent => absent, List.not_mem_nil, grant, ?_, rfl, rfl, initial_permission⟩
    change Function.update (Function.update starting.grants 5 (some grant)) 6 (some grant) 5 = some grant
    rw [Function.update_of_ne (by decide : 5 ≠ 6), Function.update_self]
  have accepted : Step host parallel (.received 7 packet) wroteFirst := .deliver firstReady rfl
  refine ⟨.cons second (.cons accepted (.nil _)), ?_, fun _ => stale_snapshot_refused ?_⟩
  · refine ⟨rfl, fun absent => absent, by decide, grant, ?_, rfl, rfl, initial_permission⟩
    change Function.update booked.grants 6 (some grant) 6 = some grant
    simp only [Function.update_self]
  · change [authored] ≠ []
    simp

end Controls

end Mettapedia.Languages.MeTTa.SpaceTheory.HeadWriteProtocol
