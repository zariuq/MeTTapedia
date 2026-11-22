import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Equivalence.RholangForms
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Weaknesses.Rights

/-!
# `select` with join arms

Rholang's `select` chooses among branches whose receipts are linear joins:

    select { p₁ <- a & q₁ <- b => P ; r <- c => Q }

`RholangForms` defines it, as the guest library does, by one parked choice over one transform per
arm that takes every bind of the arm:

    select { … arm … } = await (choose (transform (, (take p₁ @ a) (take q₁ @ b)) P) …)

and proves that Rholang's rules and these definitions correspond exactly
(`Rholang.rholang_correspond`), so bisimilarity is preserved and reflected
(`Rholang.bisimilar_rholang_iff`). A select whose arms bind one channel each is the fragment of arms
with no further bind (`Rholang.oneBind`, `Rholang.select_oneBind`).

## Controls

A join arm commits its whole receipt in one step: the select's rule takes the select and one message
per bind (`Controls.join_arm_takes_all`). Encoding a join arm by its first bind alone, as a one-bind
arm would be, identifies a select over a join with a select over a single receive, so that encoding
is not injective and cannot be exact (`Controls.firstBind_not_injective`); the encoding of
`RholangForms` tells them apart (`Controls.encode_separates`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Equivalence.Rholang.SelectJoins

open Agents

namespace Controls

/-- A two-channel join arm and a one-bind arm over the same first bind. -/
def joinArm : Arm Nat Unit Unit := ((0, ()), [(1, ())], ())
def singleArm : Arm Nat Unit Unit := ((0, ()), [], ())

/-- **Positive**: the select over a join arm takes the select and one message on each channel, in
one rule. -/
theorem join_arm_takes_all :
    RhoRule (Ch := Nat) (Val := Nat) (fun _ _ => True) (fun _ _ => 0)
      ⟨(([.recv (.select [joinArm]), .msg 0 7, .msg 1 8] : List (RhoLbl Nat Nat Unit Unit)) :
          Multiset (RhoLbl Nat Nat Unit Unit)), 0, 0, fun _ => false⟩ := by
  have := RhoRule.select (Ch := Nat) (Val := Nat) (sat := fun _ _ => True) (body := fun _ _ => 0)
    (arms := [joinArm]) (b := (0, ())) (bs := [(1, ())]) (k := ()) (vals := [7, 8])
    (List.mem_singleton.mpr rfl) (List.Forall₂.cons trivial (List.Forall₂.cons trivial List.Forall₂.nil))
  simpa [msgs] using this

/-- **Positive**: a select over one-bind arms takes the select and one message, as Rholang's
one-bind `select` does. -/
theorem single_arm_takes_one :
    RhoRule (Ch := Nat) (Val := Nat) (fun _ _ => True) (fun _ _ => 0)
      ⟨{.recv (.select ([((0 : Nat), (), ())].map oneBind)), .msg 0 7}, 0, 0, fun _ => false⟩ :=
  select_oneBind (List.mem_singleton.mpr rfl) trivial

/-- The encoding of an arm by its first bind alone. -/
def firstBindTr (a : Arm Nat Unit Unit) : Tr Nat Unit Unit := ⟨asSources .take [a.1], a.2.2⟩

/-- **Negative**: encoded by first binds, a select over a join arm and a select over a single
receive become the same parked choice, so that encoding is not injective. -/
theorem firstBind_not_injective :
    (Agent.choose ([joinArm].map firstBindTr) : Agent (Tr Nat Unit Unit)) =
      Agent.choose ([singleArm].map firstBindTr) ∧
    (Recv.select [joinArm] : Recv Nat Unit Unit) ≠ Recv.select [singleArm] := by
  refine ⟨rfl, ?_⟩
  decide

/-- The encoding of `RholangForms` tells them apart. -/
theorem encode_separates :
    encodeRecv (Recv.select [joinArm] : Recv Nat Unit Unit) ≠ encodeRecv (Recv.select [singleArm]) := by
  decide

section PreparedReceive

open Prepared
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Weaknesses.Rights (prepareReceiveBinds)

private def narrow : Datum Nat := ⟨7, 0, false⟩
private def wide : Datum Nat := ⟨9, 1, false⟩
private def candidates : Nat → List (Datum Nat)
  | 0 => [narrow, wide]
  | _ + 1 => [wide]

private def capture (any : Bool) (raw : Nat) : Option (List Nat) :=
  if any || raw == 7 then some [raw + 100] else none

private def twoBinds : List (Nat × Bool) := [(0, false), (1, true)]
private def twoMatches : List (Match Nat Nat) := [⟨narrow, [107]⟩, ⟨wide, [109]⟩]

/-- The worker visits channel 1 first, but returns channel 0's bindings
first. The continuation's index zero refers to the last pushed capture;
it never receives the raw datum in place of the matched value. -/
theorem prepared_packet_keeps_bind_order :
    packet capture twoBinds candidates = some twoMatches ∧
    twoMatches.map (fun row => row.datum.raw) = [7, 9] ∧
    dispatchEnv twoMatches = [109, 107] := by
  decide +kernel

/-- Distinct source channel expressions can resolve to the same store
channel. On this candidate order the greedy worker uses the only narrow
datum for the flexible bind. A globally valid joined match still exists. -/
theorem resolved_alias_can_miss_an_admissible_pair :
    (twoBinds.map Prod.fst).Nodup ∧
    let aliases := twoBinds.map (fun bind => ((0 : Nat), bind.2))
    prepareReceiveBinds [((0 : Nat), none, false), (1, some (⟨true, false⟩, 0), true)] = some aliases ∧
    packet capture aliases candidates = none ∧
    List.Forall₂ (Fits capture candidates) aliases twoMatches ∧
    (twoMatches.map fun matched => matched.datum.index).Nodup := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, ?_, by decide +kernel⟩
  exact .cons ⟨by decide, rfl⟩ (.cons ⟨by decide, rfl⟩ .nil)

theorem unreadable_bundle_never_submits_the_join :
    prepareReceiveBinds [((0 : Nat), none, false), (1, some (⟨false, true⟩, 0), true)] = none := by
  decide +kernel

/-- Persistence keeps the matched datum in the speculative suffix. It
does not restore entries the scanner has already passed in that bucket. -/
theorem persistent_pick_retains_the_suffix :
    let shared := { narrow with persistent := true }
    pick capture false [wide, shared, wide] = some (⟨shared, [107]⟩, [shared, wide]) := by
  decide +kernel

private def peekBody (_ : Unit) (_ : List Nat) : Multiset (RhoLbl Nat Nat Bool Unit) :=
  {.msg 2 107}

private def samplePeek : Rule (RhoLbl Nat Nat Bool Unit) :=
  ⟨{.recv (.receipt .peek (0, false) [(1, true)] ())}, {.msg 0 7, .msg 1 9}, peekBody () [7, 9],
    fun _ => false⟩

private def mixedPacket : List (Match Nat Nat) :=
  [⟨narrow, [107]⟩, ⟨{ wide with persistent := true }, [109]⟩]

/-- The locked cut loses the linear raw row `7`, keeps the persistent
one, and does not store the capture `107` as a replacement. Only the
settled step has the surface read observation. -/
theorem split_peek_has_an_observable_cut :
    let held := peekReposts (K := Unit) twoBinds mixedPacket
    let cut := (detachPeek samplePeek held).result samplePeek.redex
    RhoRule (fun pat val => (capture pat val).isSome) peekBody samplePeek ∧
    held = {.msg 0 7} ∧
    Reduces (· = detachPeek samplePeek held) samplePeek.redex cut ∧
    cut = {.msg 1 9} ∧
    samplePeek.result samplePeek.redex ≠ cut := by
  let held := peekReposts (K := Unit) twoBinds mixedPacket
  have accepted : Accepts (fun pat val => (capture pat val).isSome) twoBinds [7, 9] :=
    .cons (by decide) (.cons (by decide) .nil)
  have surface : RhoRule (fun pat val => (capture pat val).isSome) peekBody samplePeek :=
    .peek accepted
  have part : held ≤ samplePeek.keep := by decide +kernel
  have admitted : samplePeek.Enabled samplePeek.redex := ⟨le_rfl, avoids_none _⟩
  exact ⟨surface, by decide +kernel, (isolated_peek_settles _ _ _ part admitted).1,
    by decide +kernel, by decide +kernel⟩

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits (Enabled fire)

private def parkedJoinData (channel : Nat) : List (Datum Nat) :=
  if channel = 1 then [wide] else []

private def offeredPacket (persist : Bool) : List (Match Nat Nat) :=
  [⟨⟨7, -1, persist⟩, [107]⟩, ⟨wide, [109]⟩]

/-- A join can use the just-offered value and a stored value without
deleting any row at the offer sentinel. When the offer is persistent the
reducer schedules only that offer again, not the other peeked row. -/
theorem persistent_offer_preempts_the_other_peek_repost :
    packet capture twoBinds parkedJoinData = none ∧
    packet capture twoBinds (withOffer parkedJoinData 0 7 true) = some (offeredPacket true) ∧
    (∃ row ∈ offeredPacket true, row.datum = ⟨7, -1, true⟩) ∧
    (lockedDataCommit twoBinds (offeredPacket true)).taken = {(1, 1)} ∧
    (lockedDataCommit twoBinds (offeredPacket true)).kept = ∅ ∧
    Enabled (fun _ => 9) {(1, 1)} (lockedDataCommit twoBinds (offeredPacket true)) ∧
    fire {(1, 1)} (lockedDataCommit twoBinds (offeredPacket true)) = ∅ ∧
    afterProduce ((0 : Nat), 7, true) true twoBinds (offeredPacket true) = [(0, 7, true)] ∧
    afterProduce ((0 : Nat), 7, false) true twoBinds (offeredPacket false) =
      [(0, 7, false), (1, 9, false)] := by
  have blocked : packet capture twoBinds parkedJoinData = none := by decide +kernel
  have fired : packet capture twoBinds (withOffer parkedJoinData 0 7 true) =
      some (offeredPacket true) := by decide +kernel
  have represented : ∀ source datum, datum ∈ parkedJoinData source → (source, datum.index) ∈ ({(1, 1)} : Finset (Nat × Int)) := by
    intro source datum present
    by_cases same : source = 1
    · subst source
      simp [parkedJoinData] at present
      subst datum
      decide
    · simp [parkedJoinData, same] at present
  have indexed : ∀ source first second, first ∈ parkedJoinData source → second ∈ parkedJoinData source →
      first.index = second.index → first = second := by
    intro source first second old other _
    by_cases same : source = 1
    · simp [parkedJoinData, same] at old other
      exact old.trans other.symm
    · simp [parkedJoinData, same] at old
  have admitted := locked_data_admitted_with_offer capture {(1, 1)} (fun _ => 9) represented indexed fired
  exact ⟨blocked, fired, arrival_used_of_blocked capture (by decide) blocked fired,
    by decide +kernel, by decide +kernel, admitted, by decide +kernel,
    by decide +kernel, by decide +kernel⟩

/-- The same incoming data can meet an ordinary or a persistent parked
receipt. In the persistent case the existing waiting key stays live.
This is different from an active request's later consume call. -/
theorem parked_persistence_keeps_the_receiver_key :
    let live : Finset (Nat × Int) := {(1, 1)}
    let waiting : Nat := 13
    let soup := live.disjSum {waiting}
    let readVal := Sum.elim (fun _ : Nat × Int => 9) (fun _ : Nat => 0)
    let received := offeredPacket true
    let linear := parkedProduceCommit twoBinds received waiting false
    let repeated := parkedProduceCommit twoBinds received waiting true
    Enabled readVal soup linear ∧ Enabled readVal soup repeated ∧
      (fire soup linear).toRight = ∅ ∧ (fire soup repeated).toRight = {waiting} ∧
      (fire soup repeated).toLeft = ∅ := by
  obtain ⟨_, _, _, _, _, dataReady, dataAfter, _, _⟩ := persistent_offer_preempts_the_other_peek_repost
  have linear := parked_produce_projects twoBinds (offeredPacket true) {(1, 1)} {13} (13 : Nat) false
  have repeated := parked_produce_projects twoBinds (offeredPacket true) {(1, 1)} {13} (13 : Nat) true
  exact ⟨parked_produce_admitted (fun _ => 0) 13 false (by simp) dataReady,
    parked_produce_admitted (fun _ => 0) 13 true (by simp) dataReady,
    linear.2.trans (by simp), repeated.2, repeated.1.trans dataAfter⟩

/-- At two selected indices in a single bucket, increasing-index deletion
is not simultaneous deletion of the original rows. This control concerns
the array operation after selection, not surface syntax acceptance. -/
theorem aliased_deletions_shift_the_later_index :
    applyStoredRemovals [(0, 0), (0, 1)] (fun _ : Nat => [7, 8, 9]) 0 = [8] ∧
      applyStoredRemovals [(0, 1), (0, 0)] (fun _ : Nat => [7, 8, 9]) 0 = [9] := by
  decide +kernel

private def takeWaiting : List (Nat × Bool) := [(0, false)]
private def linearOfferPacket : List (Match Nat Nat) := [⟨⟨7, -1, false⟩, [107]⟩]

/-- The next consume is blocked while the original data is out of the
store. The actual repost request then prepares an enabled linear receive
on its virtual offer. It is not an idle store insertion. -/
theorem repost_can_wake_a_waiting_take :
    let empty : Nat → List (Datum Nat) := fun _ => []
    let repost := (afterConsume () false true twoBinds mixedPacket).2
    let offered := repost.head?.bind fun (channel, raw, persistent) =>
      packet capture takeWaiting (withOffer empty channel raw persistent)
    repost = [(0, 7, false)] ∧ packet capture takeWaiting empty = none ∧
    offered = some linearOfferPacket ∧
    (lockedDataCommit takeWaiting linearOfferPacket).taken = ∅ ∧
    ∃ rule : Rule (TLbl Nat Nat Bool Unit),
      Fires (trRows (fun pat raw => (capture pat raw).isSome)
        fun k vals => (peekBody k vals).map encode) rule ∧
      rule.Enabled (({.recv (.receipt .linear (0, false) [] ()), .msg 0 7} :
        Multiset (RhoLbl Nat Nat Bool Unit)).map encode) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  have delivered : packet capture ((0, false) :: []) (withOffer (fun _ : Nat => []) 0 7 false) =
      some linearOfferPacket := by decide +kernel
  obtain ⟨rule, redex, _, _, lowered⟩ :=
    packet_prepares_transform_receipt capture peekBody .linear (0, false) [] () _ _ delivered
  refine ⟨rule.mapPos encode, lowered, ?_⟩
  constructor
  · rw [mapPos_redex, redex]
    rfl
  · exact avoids_none _

private def repeatRequest : List (Nat × Bool) × Unit := ([(0, true)], ())
private def firstDelivery : List (Match Nat Nat) := [⟨narrow, [107]⟩]
private def secondDelivery : List (Match Nat Nat) := [⟨wide, [109]⟩]

/-- An active persistent receive searches again after its first removal.
Here it accepts two different stored occurrences, then has no packet and
can become a waiting continuation. Physical keys are relative to the
represented cut, not an assertion about stable Rust vector indices. -/
theorem repeated_active_receive_searches_the_reached_view :
    let rows := [narrow, wide]
    let live : Finset (Nat × Int) := {(0, 0), (0, 1)}
    let first := lockedDataCommit repeatRequest.1 firstDelivery
    let once := fire live first
    let remaining := rows.filter fun datum => (0, datum.index) ∈ once
    let recheck := (afterConsume repeatRequest true false repeatRequest.1 firstDelivery).1
    let second := lockedDataCommit repeatRequest.1 secondDelivery
    let twice := fire once second
    packet capture repeatRequest.1 (fun _ => rows) = some firstDelivery ∧
    Enabled (fun _ => 0) live first ∧ recheck = some repeatRequest ∧
    (recheck.bind fun request => packet capture request.1 (fun _ => remaining)) = some secondDelivery ∧
    Enabled (fun _ => 0) once second ∧
    packet capture repeatRequest.1 (fun _ => rows.filter fun datum => (0, datum.index) ∈ twice) = none := by
  decide +kernel

/-! ## Body entry after communication and `new` -/

private def seedPacket (receiver first : Nat) (more : List Nat) : Nat :=
  more.foldl (fun acc seed => 10 * acc + seed) (10 * receiver + first)

/-! ## Locked misses and the next array view -/

private def coldArray (channel : Nat) : List (Datum Nat) :=
  if channel = 1 then [⟨9, 0, false⟩] else []

private def registeredBinds (_ : Nat) : List (Nat × Bool) := twoBinds

/-- Park a two-bind receive, store a send that still cannot complete
the join, then wake it on the other channel. The stored send owns a
fresh occurrence key; only its new native coordinate is zero. The
earlier index-zero row survives the wake, at its refreshed input-cut
coordinate. A later native cut refreshes array positions again. -/
theorem park_store_and_wake_at_refreshed_indices :
    let data : Finset (Nat × Int) := {(1, 0)}
    let initial := data.disjSum (∅ : Finset Nat)
    let park : Commit ((Nat × Int) ⊕ Nat) Nat := Commit.makeOne (.inr 13)
    let parked := fire initial park
    let offer : ProduceRequest Nat Nat := (1, 8, false)
    let store : Commit ((Nat × Int) ⊕ Nat) Nat := Commit.makeOne (.inl (1, 2))
    let inserted := fire parked store
    let nextView := putDatumView coldArray offer
    let next := (inserted.toLeft.image (slotAfterPut 1 2)).disjSum inserted.toRight
    let wake : ProduceRequest Nat Nat := (0, 7, false)
    let selected : List (Match Nat Nat) := [⟨⟨7, -1, false⟩, [107]⟩, ⟨⟨8, 0, false⟩, [108]⟩]
    let deliver := parkedProduceCommit twoBinds selected (13 : Nat) false
    let body (_ : Nat) : Nat × Nat := (42, 1)
    let effects : DispatchBatch (Nat × EvalScope Nat Nat) Empty (ProduceRequest Nat Nat) :=
      ⟨(42, ⟨[107, 108], 0, 178⟩), none, [], false⟩
    lockedConsume capture id seedPacket 42 1 () false false twoBinds coldArray (13 : Nat) = some (park, none) ∧
    Enabled (fun _ => 0) initial park ∧ parked.toRight = {13} ∧
    lockedProduce capture id seedPacket registeredBinds body (fun _ => false) (fun _ => false)
      offer [(coldArray, [13])] 2 = some (store, none) ∧
    Enabled (fun _ => 0) parked store ∧ inserted.toLeft = {(1, 0), (1, 2)} ∧
    nextView 1 = [⟨8, 0, false⟩, ⟨9, 1, false⟩] ∧
    lockedProduce capture id seedPacket registeredBinds body (fun _ => false) (fun _ => false)
      wake [(nextView, [13])] 2 = some (deliver, some effects) ∧
    Enabled (fun _ => 0) next deliver ∧
    (fire next deliver).toLeft = {(1, 1)} ∧ (fire next deliver).toRight = ∅ := by
  exact ⟨rfl, by decide +kernel, by decide +kernel, rfl, by decide +kernel, by decide +kernel,
    rfl, rfl, by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- Hiding a registered bucket changes the decision with the same
data. A missing index entry does not prove a missing match. -/
theorem omitted_join_is_not_absence :
    let offer : ProduceRequest Nat Nat := (0, 7, false)
    let live : Finset (Nat × Int) := {(1, 0)}
    let installed : Finset Nat := {13}
    let hidden : List (WaitView Nat Nat Nat) := []
    offerSearch capture registeredBinds offer hidden = none ∧
    (offerSearch capture registeredBinds offer [(coldArray, [13])]).isSome ∧
    ReadyOn capture (offeredValues (StoredValue live (fun _ => 9)) offer) (registeredBinds 13) ∧
    ¬ (∀ w : Nat, (w ∈ installed ∧ offer.1 ∈ (registeredBinds w).map Prod.fst) ↔
      ∃ group ∈ hidden, w ∈ group.2) := by
  refine ⟨rfl, by decide +kernel, ?_, ?_⟩
  · intro slot inside
    simp only [registeredBinds, twoBinds, List.mem_cons, List.not_mem_nil, or_false] at inside
    rcases inside with rfl | rfl
    · exact ⟨7, .inr ⟨rfl, rfl⟩, [107], rfl⟩
    · exact ⟨9, .inl ⟨0, by decide, rfl⟩, [109], rfl⟩
  · intro covered
    obtain ⟨group, visible, _⟩ := (covered 13).mp (by decide)
    simp at visible

/-! ## Ordered offer selection and launching follow-ups -/

private def nativeIdentity (waiter : Nat) : Nat :=
  if waiter = 13 then 12 else waiter

/-- Starting from the empty index, install a waiter, park an ordinary
waiter of the same joint shape, and repeat the latter request under
a proposed new key. The repeated miss keeps the old occurrence.
The ordinary wake uses its combined-list slot, then retains the
installed route and both native index entries. -/
theorem duplicate_park_and_linear_wake_keep_live_index :
    let keys : List Nat := [0, 1]
    let installed := (JoinIndex.empty : JoinIndex Nat Nat).install keys 50
    let parked := installed.park nativeIdentity keys 12
    let repeated := parked.park nativeIdentity keys 13
    let after := repeated.dropOrdinary keys 12
    let incoming : ProduceRequest Nat Nat := (0, 7, false)
    let groups := repeated.offerViews 0 (fun bucket _ => (coldArray, repeated.waitersAt bucket))
    let selected : List (Match Nat Nat) := [⟨⟨7, -1, false⟩, [107]⟩, ⟨⟨9, 0, false⟩, [109]⟩]
    let work : DispatchBatch (Nat × EvalScope Nat Nat) Empty (ProduceRequest Nat Nat) :=
      ⟨(42, ⟨[107, 109], 0, 179⟩), none, [], false⟩
    let first : Commit ((Nat × Int) ⊕ Nat) Nat := Commit.makeOne (.inr 12)
    let duplicate : Commit ((Nat × Int) ⊕ Nat) Nat := Commit.keepOne (.inr 12)
    let wake := parkedProduceCommit twoBinds selected (12 : Nat) false
    let data : Finset (Nat × Int) := {(1, 0)}
    let before := data.disjSum ({50} : Finset Nat)
    let next := fire before first
    let channels := fun w => (registeredBinds w).map Prod.fst
    installed.Covers channels before.toRight ∧
    lockedIndexedConsume capture id seedPacket 42 1 () false false registeredBinds coldArray
      (12 : Nat) installed nativeIdentity = some (first, none) ∧
    Enabled (fun _ => 0) before first ∧ parked.Covers channels next.toRight ∧
    lockedIndexedConsume capture id seedPacket 42 1 () false false registeredBinds coldArray
      (13 : Nat) parked nativeIdentity = some (duplicate, none) ∧
    Enabled (fun _ => 0) next duplicate ∧ fire next duplicate = next ∧
    repeated.waitersAt keys = [50, 12] ∧
    lockedProduce capture id seedPacket registeredBinds (fun _ => (42, 1)) (· == 50) (fun _ => false)
      incoming groups 2 = some (wake, some work) ∧
    Enabled (fun _ => 0) next wake ∧ after.Covers channels (fire next wake).toRight ∧
    (repeated.waitersAt keys)[1]? = some 12 ∧
    (repeated.ordinary keys).eraseIdx 1 = [12] ∧
    after.waitersAt keys = [50] ∧ after.keysAt 0 = [keys, keys] := by
  dsimp only
  let keys : List Nat := [0, 1]
  let channels := fun w => (registeredBinds w).map Prod.fst
  let installed := (JoinIndex.empty : JoinIndex Nat Nat).install keys 50
  let parked := installed.park nativeIdentity keys 12
  let repeated := parked.park nativeIdentity keys 13
  have h₀ : installed.Covers channels ({50} : Finset Nat) := by
    have step := JoinIndex.install_covers (JoinIndex.empty_covers channels) 50 (by simp)
    simpa [installed, JoinIndex.empty, keys, channels, registeredBinds, twoBinds] using step
  have h₁ : parked.Covers channels (insert 12 ({50} : Finset Nat)) := by
    have step := JoinIndex.park_covers h₀ nativeIdentity 12 (fun _ => by decide)
    exact step
  have h₂ : repeated.Covers channels (insert 12 ({50} : Finset Nat)) := by
    have step := JoinIndex.park_covers h₁ nativeIdentity 13 (fun _ => by decide)
    exact step
  have h₃ : (repeated.dropOrdinary keys 12).Covers channels
      ((insert 12 ({50} : Finset Nat)).erase 12) :=
    JoinIndex.drop_covers h₂ 12 (by decide +kernel)
  refine ⟨?_, rfl, by decide +kernel, ?_, rfl, by decide +kernel, by decide +kernel, rfl, rfl,
    by decide +kernel, ?_, rfl, rfl, rfl, rfl⟩
  · exact h₀
  · have shape : (fire ((({(1, 0)} : Finset (Nat × Int)).disjSum ({50} : Finset Nat)))
        (Commit.makeOne (R := Nat) (.inr 12))).toRight = insert 12 ({50} : Finset Nat) := by decide +kernel
    rw [shape]
    exact h₁
  · have gone : (insert 12 ({50} : Finset Nat)).erase 12 = {50} := by decide +kernel
    rw [gone] at h₃
    exact h₃

/-- Removing the last ordinary receipt deletes that ordered vector
from the lookup, without touching a different join sharing a channel. -/
theorem last_linear_waiter_retires_only_its_vector :
    let start := (JoinIndex.empty : JoinIndex Nat Nat).park id [0, 1] 12
    let withNeighbor := start.park id [0, 2] 16
    let after := withNeighbor.dropOrdinary [0, 1] 12
    withNeighbor.keysAt 0 = [[0, 2], [0, 1]] ∧
      after.keysAt 0 = [[0, 2]] ∧ after.keysAt 1 = [] ∧
      after.waitersAt [0, 2] = [16] := by
  exact ⟨rfl, rfl, rfl, rfl⟩

private def emptyBucket (waiters : List Nat) : WaitView Nat Nat Nat := (fun _ => [], waiters)

private def offerBinds (waiter : Nat) : List (Nat × Bool) :=
  if waiter = 20 then [(0, true), (2, true)] else [(0, waiter != 14)]

private def waitingViews : List (WaitView Nat Nat Nat) :=
  [emptyBucket [20], emptyBucket [11, 12, 14]]

private def packetEight : List (Match Nat Nat) := [⟨⟨8, -1, false⟩, [108]⟩]

/-- Search skips an entire failing join and the last-shuffled nonmatching
waiter in the next bucket. It takes just the first ready waiter, not all
matching waiters, and launches the body and the raw repost separately. -/
theorem locked_search_leaves_other_waiters_for_reposts :
    let waiters : Finset Nat := {11, 12, 14, 20}
    let before := (∅ : Finset (Nat × Int)).disjSum waiters
    let offer : ProduceRequest Nat Nat := (0, 8, false)
    let cut := parkedProduceCommit (offerBinds 12) packetEight 12 false
    offerGroup capture offerBinds offer (emptyBucket [20]) = none ∧
    packet capture (offerBinds 14) (withOffer (fun _ => []) 0 8 false) = none ∧
    offerSearch capture offerBinds offer waitingViews = some (12, packetEight) ∧
    Enabled (Sum.elim (fun _ => 0) (fun _ => 0)) before cut ∧
    (fire before cut).toRight = {11, 14, 20} ∧
    prepareProduceBatch id seedPacket 42 1 offer true (offerBinds 12) packetEight =
      some ⟨(42, ⟨[108], 0, 18⟩), none, [(0, 8, false)], true⟩ := by
  have chosen : offerSearch capture offerBinds (0, 8, false) waitingViews = some (12, packetEight) :=
    by decide +kernel
  have represented : ∀ group ∈ waitingViews, ∀ source datum, datum ∈ group.1 source →
      (source, datum.index) ∈ (∅ : Finset (Nat × Int)) ∧ (0 : Nat) = datum.raw := by
    intro group member source datum live
    simp only [waitingViews, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> simp [emptyBucket] at live
  have unique : ∀ group ∈ waitingViews, ∀ source first second,
      first ∈ group.1 source → second ∈ group.1 source → first.index = second.index → first = second := by
    intro group member source first second live _ _
    have impossible := (represented group member source first live).1
    simp at impossible
  have registered : ∀ group ∈ waitingViews, ∀ waiter ∈ group.2, waiter ∈ ({11, 12, 14, 20} : Finset Nat) := by
    intro group member waiter live
    simp only [waitingViews, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · simp [emptyBucket] at live
      subst waiter
      decide
    · simp [emptyBucket] at live
      rcases live with rfl | rfl | rfl <;> decide
  obtain ⟨enabled, _, retained, _⟩ := selected_offer_admits_and_dispatches capture id seedPacket
    (fun _ => ((42 : Nat), 1)) (fun _ => false) (fun _ => true)
    ∅ {11, 12, 14, 20} (fun _ => 0) (fun _ => 0) represented unique registered (by decide +kernel) chosen
  exact ⟨by decide +kernel, by decide +kernel, chosen, enabled,
    retained.trans (by decide +kernel), by decide +kernel⟩

/-- The first successful rendezvous can make either sibling's send win
under a scheduler permitting either ready effect first. This is a
separation of the two handoff traces, not a claim about Rust poll order. -/
theorem repost_and_body_can_compete_for_the_same_waiter :
    let binds : Nat → List (Nat × Bool) := fun _ => [(0, true)]
    let initial := [emptyBucket [2, 1]]
    let before := (∅ : Finset (Nat × Int)).disjSum ({1, 2} : Finset Nat)
    let gate := parkedProduceCommit (binds 1) linearOfferPacket 1 false
    let cut := fire before gate
    let repost : ProduceRequest Nat Nat := (0, 7, false)
    let bodySend : ProduceRequest Nat Nat := (0, 8, false)
    let waitAfter := [emptyBucket [2]]
    let firstRepost := parkedProduceCommit (binds 2) linearOfferPacket 2 false
    let firstBody := parkedProduceCommit (binds 2) packetEight 2 false
    offerSearch capture binds repost initial = some (1, linearOfferPacket) ∧
    Enabled (fun _ => 0) before gate ∧ cut.toRight = {2} ∧
    (prepareProduceBatch id seedPacket 42 1 repost true (binds 1) linearOfferPacket).map
      DispatchBatch.produces = some [repost] ∧
    offerSearch capture binds repost waitAfter = some (2, linearOfferPacket) ∧
    offerSearch capture binds bodySend waitAfter = some (2, packetEight) ∧
    Enabled (fun _ => 0) cut firstRepost ∧ Enabled (fun _ => 0) cut firstBody ∧
    fire cut firstRepost = ∅ ∧ fire cut firstBody = ∅ ∧
    ¬ Enabled (fun _ => 0) (fire cut firstRepost) firstBody ∧
    ¬ Enabled (fun _ => 0) (fire cut firstBody) firstRepost ∧
    offerSearch capture binds repost [] = none ∧ offerSearch capture binds bodySend [] = none ∧
    dispatchEnv linearOfferPacket ≠ dispatchEnv packetEight := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

private def errorDigits (faults : List Nat) : Nat := faults.foldl (fun acc fault => 10 * acc + fault) 0

/-- A peek with no linear datum to repost is still joined. A joined
failure waits for all workers; aggregates reflect the order of the
launch slots, and abort outranks exhausted credit. -/
theorem joined_return_is_not_completion_order_or_direct_dispatch :
    let selected : List (Match Nat Nat) := [⟨⟨7, 0, true⟩, [107]⟩]
    let direct := prepareConsumeBatch id seedPacket 42 1 takeWaiting false false takeWaiting selected
    let peek := prepareConsumeBatch id seedPacket 42 1 takeWaiting false true takeWaiting selected
    let repeated := prepareConsumeBatch id seedPacket 42 1 takeWaiting true true takeWaiting selected
    let dispatch : Nat × EvalScope Nat Nat := (42, ⟨[107], 0, 17⟩)
    let joined : DispatchBatch (Nat × EvalScope Nat Nat) (List (Nat × Bool)) (ProduceRequest Nat Nat) :=
      ⟨dispatch, some takeWaiting, [], true⟩
    let emptySlots : Fin joined.jobs.length → Option (Except Nat Nat) := fun _ => none
    let body : Fin joined.jobs.length := ⟨0, by decide +kernel⟩
    let again : Fin joined.jobs.length := ⟨1, by decide +kernel⟩
    let report := joined.report 0 0 3 errorDigits
    direct.map DispatchBatch.joined = some false ∧
    peek = some ⟨dispatch, none, [], true⟩ ∧ repeated = some joined ∧
    (direct.bind fun b => b.report 0 0 3 errorDigits (fun _ => some (.ok 5))) =
      some (.ok 5) ∧
    (peek.bind fun b => b.report 0 0 3 errorDigits (fun _ => some (.ok 5))) =
      some (.ok 0) ∧
    report (Function.update emptySlots body (some (.error 0))) = none ∧
    report (Function.update (Function.update emptySlots again (some (.error 2)))
      body (some (.error 1))) = some (.error 12) ∧
    report (Function.update (Function.update emptySlots body (some (.error 3)))
      again (some (.error 0))) = some (.error 0) := by
  decide +kernel

private def nameDraw (seed : Nat) : Nat × Nat := (seed, seed + 1)

private def chargeTest (cost : Nat) (balance : Int) : Int × Except String Unit :=
  if balance < 0 then (balance, .error "charge") else
    let left := balance - (cost : Int)
    (left, if left < 0 then .error "charge" else .ok ())

private def testUris : Nat → Except String Nat :=
  resolveNewUri (fun uri => if uri < 2 then some 70 else none)
    (fun uri => if uri == 2 then .ok 80 else .error "URI")

/-- A selected join enters the body with captures in its scope and the
packet's random states in bind order. A following `new` retains both
old captures, installs two private draws, then two (aliasing) URIs. -/
theorem receive_then_new_retains_scope :
    let entered := (packet capture twoBinds candidates).bind (processDispatch id seedPacket 42 1)
    let body := entered.map fun (code, scope) =>
      openNew chargeTest nameDraw testUris 2 [0, 1] code scope 100
    let installed : EvalScope Nat Nat := ⟨[107, 109, 179, 180, 70, 70], 0, 181⟩
    entered = some (42, ⟨[107, 109], 0, 179⟩) ∧
      body = some (82, .ok (42, installed)) ∧
      ([0, 1, 2, 3, 4, 5, 6].map (shiftedLookup installed.stored installed.shift) =
        [some 70, some 70, some 180, some 179, some 109, some 107, none]) := by
  decide +kernel

/-- A registered URI overrides an injection; URI-only scopes do not
consume a private draw. Bad resolution gives no body after charging.
An earlier charge failure takes precedence over unresolved URIs. -/
theorem uri_resolution_and_charge_are_distinct :
    let start : EvalScope Nat Nat := ⟨[90], 1, 10⟩
    testUris 0 = .ok 70 ∧ testUris 2 = .ok 80 ∧
      openNew chargeTest nameDraw testUris 0 [2] true start 100 =
        (88, .ok (true, ⟨[90, 80], 1, 10⟩)) ∧
      openNew chargeTest nameDraw testUris 1 [3] true start 30 = (16, .error "URI") ∧
      openNew chargeTest nameDraw testUris 1 [3] true start 5 = (-9, .error "charge") := by
  decide +kernel

/-- Lifting ambient indices below the shift is not a scope law: those
indices name holes until binding. The valid ambient index still reads
the old value under the full lift. -/
theorem new_does_not_lift_uninstalled_slots :
    shiftedLookup ([10] : List Nat) 1 0 = none ∧
      shiftedLookup ([10, 20] : List Nat) 1 0 = none ∧
      shiftedLookup ([10, 20] : List Nat) 1 (1 + 0) = some 20 ∧
      shiftedLookup ([10, 20] : List Nat) 1 (1 + 1) = some 10 := by
  decide +kernel

/-- Opening does not turn a repeated generator value into two different
private names. Freshness must come from the supply's actual contract. -/
theorem repeated_draws_are_not_fresh :
    let start : EvalScope Nat Nat := ⟨[], 0, 10⟩
    let repeated := fun seed : Nat => ((7 : Nat), seed + 1)
    let opened : EvalScope Nat Nat := ⟨[7, 7], 0, 12⟩
    openNew chargeTest repeated testUris 2 [] true start 100 = (86, .ok (true, opened)) ∧
      shiftedLookup opened.stored opened.shift 0 = shiftedLookup opened.stored opened.shift 1 := by
  decide +kernel

end PreparedReceive

end Controls

end Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Equivalence.Rholang.SelectJoins
