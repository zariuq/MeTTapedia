import Mettapedia.GSLT.Dynamics.CacheCoherence
import Mettapedia.Machines.OrderedDependencyProjection
import Mettapedia.Machines.OrderedDependencyOverlay

/-!
# Cache keys derived from ordered dependency stores

The read stamps of the ordered dependency store, of its projections and of its
overlays are instances of the notification form of scoped cache coherence.
Their soundness as keys is derived from the actual transitions: every content
update advances the revision of its owner and of every reverse-indexed reader,
every topology change advances the changed reader, and revisions never
decrease. Nothing about the desired conclusion is assumed.

* **Positive.** The read stamp is a `SoundKey` for the ordered query on the
  points of one run (`readStamp_soundKey_run`) and across sessions with
  distinct store identities (`readStamp_soundKey_sessions`); the same holds for
  projection stamps (`projectionStamp_soundKey_run`) and overlay stamps
  (`overlayStamp_soundKey_run`). A prefix certificate certifies the prefix it
  names (`prefix_certifies_prefix`). Content readings of the reader and of
  every consulted source, in dependency order, determine the query
  (`composed_determined`).
* **What a key must contain**, each shown by a counterexample:
  - the query identity: a numeric revision or a global epoch alone is not a key
    (`Controls.revision_alone_not_key`, `Controls.epoch_alone_not_key`);
  - the projection identity (`Controls.slot_free_stamp_not_key`);
  - the session identity (`Controls.identity_reuse_not_key`);
  - the overlay's own clock: an overlay publication changes the answer without
    changing the store's revision or epoch (`Controls.overlay_change_not_key`);
  - the order of the dependencies (`Controls.unordered_dependencies_not_key`);
  - empty sources, for negative lookups
    (`Controls.contributing_sources_miss_absence`);
  - the reverse notification (`Controls.writer_only_update_does_not_notify`);
  - full currency rather than a prefix (`Controls.prefix_does_not_certify_full`).
* **Separate obligations.** A key is not a read window
  (`Controls.torn_read_after_single_check`,
  `Controls.reordered_read_after_double_check`), and owner lifetime is not
  currency (`Controls.lifetime_key_not_currency`).

These are theorems about the finite store model, not about any C realization.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.OrderedDependencyCacheKeys

open Mettapedia.GSLT.Dynamics.MemoizationObserver (SoundKey)
open Mettapedia.GSLT.Core.NonFactorization
open Mettapedia.GSLT.Dynamics.CacheCoherence
open Mettapedia.Machines.OrderedDependencyStore

variable {Entry : Type} {size : Nat}

/-! ## The store -/

theorem execute_eq (s : Store Entry size) (actions : List (Action Entry size)) :
    OrderedDependencyStore.execute s actions =
      Mettapedia.GSLT.Dynamics.CacheCoherence.execute OrderedDependencyStore.step s actions := by
  induction actions generalizing s with
  | nil => rfl
  | cons action rest ih => exact ih _

theorem setDependencies_identity (s : Store Entry size) (reader : Fin size)
    (deps : List (Fin size)) : (setDependencies s reader deps).identity = s.identity := by
  unfold setDependencies
  split <;> rfl

theorem step_identity (s : Store Entry size) (action : Action Entry size) :
    (OrderedDependencyStore.step s action).identity = s.identity := by
  cases action with
  | append source suffix => rfl
  | replace source contents => rfl
  | link reader source =>
      simp only [OrderedDependencyStore.step, link]
      split
      · rfl
      · exact setDependencies_identity _ _ _
  | unlink reader source => exact setDependencies_identity _ _ _
  | retire source => rfl
  | importModule reader source => exact setDependencies_identity _ _ _

/-- **The store notifies its readers**: the transition-level facts of the
store are exactly the notification premises. -/
theorem store_notifies :
    Notifies (OrderedDependencyStore.step (Entry := Entry) (size := size)) ObserverInvariant
      (fun s reader => (s.members reader).revision) (fun s reader => view s reader) where
  preserves := fun s action holds => step_observers s holds action
  monotone := fun s action reader => step_revision_mono s action reader
  notifies := fun s action reader holds same => step_view_of_revision_eq s holds action reader same

theorem readStamp_determines (first second : Store Entry size) (reader reader' : Fin size)
    (same : readStamp first reader = readStamp second reader') :
    first.identity = second.identity ∧ reader = reader' ∧
      (first.members reader).revision = (second.members reader').revision := by
  simp only [readStamp, ReadStamp.mk.injEq] at same
  exact ⟨same.1, same.2.1, same.2.2.2⟩

/-- **The read stamp is a sound key for the ordered query on one run.** -/
theorem readStamp_soundKey_run (origin : Store Entry size) (holds : ObserverInvariant origin)
    (actions : List (Action Entry size)) :
    SoundKey
      (fun point : Nat × Fin size =>
        readStamp (runAt OrderedDependencyStore.step origin actions point.1) point.2)
      (fun point => query (runAt OrderedDependencyStore.step origin actions point.1) point.2) := by
  simp only [query_eq_view]
  exact store_notifies.soundKey_run holds actions readStamp
    (fun first second reader reader' same =>
      let ⟨_, sameReader, counted⟩ := readStamp_determines first second reader reader' same
      ⟨sameReader, counted⟩)

/-- **Across sessions**, store identities must differ. -/
theorem readStamp_soundKey_sessions {Session : Type} (origin : Session → Store Entry size)
    (actions : Session → List (Action Entry size))
    (holds : ∀ session, ObserverInvariant (origin session))
    (distinct : Function.Injective fun session => (origin session).identity) :
    SoundKey
      (fun point : Session × Nat × Fin size =>
        readStamp (runAt OrderedDependencyStore.step (origin point.1) (actions point.1)
          point.2.1) point.2.2)
      (fun point => query (runAt OrderedDependencyStore.step (origin point.1)
        (actions point.1) point.2.1) point.2.2) := by
  simp only [query_eq_view]
  exact store_notifies.soundKey_sessions origin actions holds Store.identity step_identity
    distinct readStamp readStamp_determines

/-! ## Prefix certificates -/

/-- **A prefix certificate certifies the prefix it names.** -/
theorem prefix_certifies_prefix (source : Fin size) :
    Certifies (OrderedDependencyStore.step (Entry := Entry)) (fun _ => True)
      (fun s => prefixStamp s source) (fun stamp s => checkPrefix s stamp)
      (fun stamp s => (s.members source).own.take stamp.ceiling) := by
  intro s actions _ accepted
  rw [← execute_eq] at accepted ⊢
  have checked := of_decide_eq_true accepted
  have same : ((OrderedDependencyStore.execute s actions).members source).prefixEpoch =
      (s.members source).prefixEpoch := checked.2.2.1.symm
  have prefixed := execute_own_prefix_of_epoch_eq s actions source same
  simp only [prefixStamp]
  rw [← List.prefix_iff_eq_take.mp prefixed, List.take_length]

/-! ## Content readings in dependency order -/

/-- The contents of a store as a reading environment: every member's own list
and its ordered dependency list. -/
def contents (s : Store Entry size) : RevisionEnvironment (Fin size) (List Entry × List (Fin size)) :=
  ⟨fun member => ((s.members member).own, (s.members member).deps)⟩

/-- The ordered query, read from content readings. -/
def composed (live : RevisionEnvironment (Fin size) (List Entry × List (Fin size)))
    (reader : Fin size) : List Entry :=
  (live.current reader).1 ++ (live.current reader).2.flatMap fun source => (live.current source).1

/-- The stores the ordered query consults: the reader and every dependency,
including those whose contribution is empty. -/
def consulted (live : RevisionEnvironment (Fin size) (List Entry × List (Fin size)))
    (reader : Fin size) : List (Fin size) :=
  reader :: (live.current reader).2

theorem composed_contents (s : Store Entry size) (reader : Fin size) :
    composed (contents s) reader = view s reader := rfl

/-- **Content readings of every consulted store determine the query.** -/
theorem composed_determined :
    ReadsDetermine (composed (Entry := Entry) (size := size)) consulted := by
  intro captured live reader agrees
  have own := agrees reader (by simp [consulted])
  have sources : ∀ source ∈ (captured.current reader).2,
      live.current source = captured.current source :=
    fun source member => agrees source (by simp [consulted, member])
  simp only [composed, own]
  congr 1
  exact List.flatMap_congr fun source member => by rw [sources source member]

/-- The content key is sound on every environment, with no session identity:
it compares the readings themselves rather than a counter that summarizes
them. -/
theorem contentKey_sound :
    SoundKey (readingKey (consulted (Entry := Entry) (size := size)))
      (fun point => composed point.1 point.2) :=
  soundKey_readingKey composed_determined

/-! ## Projections -/

section Projection

open OrderedDependencyProjection

variable {Projection Value : Type} [DecidableEq Value]

theorem projection_notifies (project : Projection → Entry → Option Value) :
    Notifies (OrderedDependencyProjection.step project (size := size))
      (fun s => ObserverInvariant s.store)
      (fun (s : State Entry Projection size) (point : Fin size × Projection) =>
        s.clocks point.2 point.1)
      (fun (s : State Entry Projection size) (point : Fin size × Projection) =>
        OrderedDependencyProjection.view project s point.1 point.2) where
  preserves := fun s action holds => OrderedDependencyProjection.step_observers project s holds action
  monotone := fun s action point =>
    OrderedDependencyProjection.step_clock_mono project s action point.1 point.2
  notifies := fun s action point holds same =>
    OrderedDependencyProjection.step_view_of_clock_eq project s holds action point.1 point.2 same

/-- **The projection stamp is a sound key on one run.** The query of a point is
a reader together with a projection slot. -/
theorem projectionStamp_soundKey_run (project : Projection → Entry → Option Value)
    (origin : State Entry Projection size) (holds : ObserverInvariant origin.store)
    (actions : List (Action Entry size)) :
    SoundKey
      (fun point : Nat × (Fin size × Projection) =>
        stamp (runAt (OrderedDependencyProjection.step project) origin actions point.1)
          point.2.1 point.2.2)
      (fun point => OrderedDependencyProjection.query project
        (runAt (OrderedDependencyProjection.step project) origin actions point.1)
          point.2.1 point.2.2) := by
  simp only [OrderedDependencyProjection.query_eq_view]
  refine (projection_notifies project).soundKey_run holds actions
    (fun s point => stamp s point.1 point.2) ?_
  intro first second point point' same
  simp only [stamp, Stamp.mk.injEq] at same
  exact ⟨Prod.ext same.2.1 same.2.2.2.1, same.2.2.2.2⟩

end Projection

/-! ## Overlays -/

section Overlay

open OrderedDependencyOverlay

theorem overlay_notifies :
    Notifies (OrderedDependencyOverlay.step (Entry := Entry) (size := size))
      (fun s => ObserverInvariant s.store) (fun s (_ : Unit) => clock s)
      (fun s (_ : Unit) => OrderedDependencyOverlay.view s) where
  preserves := fun s action holds => OrderedDependencyOverlay.step_observers s holds action
  monotone := fun s action _ => OrderedDependencyOverlay.step_clock_mono s action
  notifies := fun s action _ holds same => OrderedDependencyOverlay.step_view_of_clock_eq s holds action same

/-- **The overlay stamp is a sound key on one run.** -/
theorem overlayStamp_soundKey_run (origin : State Entry size)
    (holds : ObserverInvariant origin.store)
    (actions : List (OrderedDependencyOverlay.Action Entry size)) :
    SoundKey
      (fun point : Nat × Unit => stamp (runAt OrderedDependencyOverlay.step origin actions point.1))
      (fun point => OrderedDependencyOverlay.query
        (runAt OrderedDependencyOverlay.step origin actions point.1)) := by
  simp only [OrderedDependencyOverlay.query_eq_view]
  refine overlay_notifies.soundKey_run holds actions (fun s _ => stamp s) ?_
  intro first second _ _ same
  simp only [stamp, Stamp.mk.injEq] at same
  exact ⟨rfl, same.2.2.2⟩

end Overlay

/-! ## Read windows over source segments -/

/-- Part zero of an ordered query is the reader's own list; part `index + 1`
is the own list of its `index`-th dependency. -/
def part (s : Store Entry size) (reader : Fin size) : Nat → Option (List Entry)
  | 0 => some (s.members reader).own
  | index + 1 => ((s.members reader).deps[index]?).map fun source => (s.members source).own

theorem part_eq_of_segments_eq {first second : Store Entry size} {reader : Fin size}
    (same : segments first reader = segments second reader) : part first reader = part second reader := by
  simp only [segments, Prod.mk.injEq] at same
  obtain ⟨own, sources⟩ := same
  funext index
  cases index with
  | zero => simp [part, own]
  | succ index =>
      have atIndex := congrArg (fun list => list[index]?) sources
      simp only [List.getElem?_map] at atIndex
      simp only [part]
      cases first_dep : (first.members reader).deps[index]? with
      | none =>
          cases second_dep : (second.members reader).deps[index]? with
          | none => rfl
          | some source => simp [first_dep, second_dep] at atIndex
      | some source =>
          cases second_dep : (second.members reader).deps[index]? with
          | none => simp [first_dep, second_dep] at atIndex
          | some source' =>
              simp only [first_dep, second_dep, Option.map_some, Option.some.injEq,
                Prod.mk.injEq] at atIndex
              simp [atIndex.2]

/-- The store notifies the parts of each query, not only their concatenation. -/
theorem store_notifies_parts :
    Notifies (OrderedDependencyStore.step (Entry := Entry) (size := size)) ObserverInvariant
      (fun s reader => (s.members reader).revision) part where
  preserves := fun s action holds => step_observers s holds action
  monotone := fun s action reader => step_revision_mono s action reader
  notifies := fun s action reader holds same =>
    part_eq_of_segments_eq (step_segments_of_revision_eq s holds action reader same)

/-- Concatenate the first `width` parts. -/
def assemble (parts : Nat → Option (List Entry)) (width : Nat) : List Entry :=
  ((List.range width).filterMap parts).flatten

/-! ## Controls -/

namespace Controls

open OrderedDependencyStore.Controls

/-- A query point: a store and a reader. -/
abbrev Point := Store Nat 3 × Fin 3

def answerOf (point : Point) : List Nat := query point.1 point.2

/-! ### Query identity -/

def revisionOnly (point : Point) : Nat := (point.1.members point.2).revision

def epochOnly (point : Point) : Nat := point.1.epoch

/-- Two modules of one store share revision zero and have different answers. -/
def sameRevision : NonTrivialFiber revisionOnly answerOf where
  left := (imported, 1)
  right := (imported, 2)
  sameShadow := by decide
  differentValue := by decide

/-- **A numeric revision alone is not a key.** -/
theorem revision_alone_not_key : ¬ SoundKey revisionOnly answerOf :=
  fun sound => sameRevision.differentValue (sound _ _ sameRevision.sameShadow)

def sameEpoch : NonTrivialFiber epochOnly answerOf where
  left := (imported, 1)
  right := (imported, 2)
  sameShadow := rfl
  differentValue := by decide

/-- **A global revision alone is not a key.** -/
theorem epoch_alone_not_key : ¬ SoundKey epochOnly answerOf :=
  fun sound => sameEpoch.differentValue (sound _ _ sameEpoch.sameShadow)

/-- Positive: the read stamp is sound on a concrete run. -/
theorem imported_run_sound :
    SoundKey
      (fun point : Nat × Fin 3 => readStamp (runAt OrderedDependencyStore.step imported
        [.append 2 [8], .append 1 [5], .link 1 2] point.1) point.2)
      (fun point => query (runAt OrderedDependencyStore.step imported
        [.append 2 [8], .append 1 [5], .link 1 2] point.1) point.2) :=
  readStamp_soundKey_run imported imported_observers _

/-! ### Session identity -/

/-- Another session that reuses the identity of `imported`. -/
def otherSession : Store Nat 3 :=
  link (initial 900 fun source => if source = 0 then [43] else if source = 2 then [7, 7] else []) 0 2

/-- The same session with a fresh identity. -/
def renumberedSession : Store Nat 3 :=
  link (initial 904 fun source => if source = 0 then [43] else if source = 2 then [7, 7] else []) 0 2

def sessionOrigin : Bool → Store Nat 3
  | true => imported
  | false => otherSession

def renumberedOrigin : Bool → Store Nat 3
  | true => imported
  | false => renumberedSession

def sessionKey (origin : Bool → Store Nat 3) (point : Bool × Nat × Fin 3) : ReadStamp 3 :=
  readStamp (runAt OrderedDependencyStore.step (origin point.1) [] point.2.1) point.2.2

def sessionAnswer (origin : Bool → Store Nat 3) (point : Bool × Nat × Fin 3) : List Nat :=
  query (runAt OrderedDependencyStore.step (origin point.1) [] point.2.1) point.2.2

def reusedIdentity : NonTrivialFiber (sessionKey sessionOrigin) (sessionAnswer sessionOrigin) where
  left := (true, 0, 0)
  right := (false, 0, 0)
  sameShadow := by decide
  differentValue := by decide

/-- **Identity reuse across sessions breaks the read stamp.** -/
theorem identity_reuse_not_key :
    ¬ SoundKey (sessionKey sessionOrigin) (sessionAnswer sessionOrigin) :=
  fun sound => reusedIdentity.differentValue (sound _ _ reusedIdentity.sameShadow)

/-- Positive: with distinct identities the same sessions are sound. -/
theorem distinct_identities_sound :
    SoundKey (sessionKey renumberedOrigin) (sessionAnswer renumberedOrigin) := by
  apply readStamp_soundKey_sessions renumberedOrigin (fun _ => [])
  · intro session
    cases session
    · exact link_observers _ (initial_observers _ _) 0 2
    · exact imported_observers
  · intro first second same
    cases first <;> cases second <;> first | rfl | (revert same; decide)

/-! ### Projection identity -/

section Projection

open OrderedDependencyProjection
open OrderedDependencyProjection.Controls

def slotFree (point : Slot) : Nat × Fin 3 × Nat × Nat :=
  let s := (stamp base 0 point)
  (s.identity, s.reader, s.generation, s.clock)

def slotAnswer (point : Slot) : List Nat := OrderedDependencyProjection.query project base 0 point

def slotFiber : NonTrivialFiber slotFree slotAnswer where
  left := .equation
  right := .declaration
  sameShadow := by decide
  differentValue := by decide

/-- **A projection stamp without its slot is not a key.** -/
theorem slot_free_stamp_not_key : ¬ SoundKey slotFree slotAnswer :=
  fun sound => slotFiber.differentValue (sound _ _ slotFiber.sameShadow)

end Projection

/-! ### Overlay clocks -/

section Overlay

open OrderedDependencyOverlay
open OrderedDependencyOverlay.Controls

/-- The store's view of an overlay: its root read stamp and the global epoch. -/
def storeOnlyKey (s : State Nat 3) : ReadStamp 3 × Nat :=
  (readStamp s.store s.reader, s.store.epoch)

def republished : State Nat 3 := OrderedDependencyOverlay.step nested (.publish [⟨1, ∅, [99, 99]⟩])

def overlayFiber : NonTrivialFiber storeOnlyKey OrderedDependencyOverlay.query where
  left := nested
  right := republished
  sameShadow := rfl
  differentValue := by decide

/-- **An overlay publication changes the answer without changing the store's
revision or epoch.** -/
theorem overlay_change_not_key : ¬ SoundKey storeOnlyKey OrderedDependencyOverlay.query :=
  fun sound => overlayFiber.differentValue (sound _ _ overlayFiber.sameShadow)

/-- Positive: the overlay stamp rejects that publication. -/
theorem overlay_stamp_rejects_publication :
    OrderedDependencyOverlay.stamp republished ≠ OrderedDependencyOverlay.stamp nested := by
  decide

end Overlay

/-! ### Dependency order -/

def threeSources : Store Nat 3 :=
  initial 905 fun source => if source = 0 then [42] else if source = 1 then [5] else [7]

def forward : Store Nat 3 := link (link threeSources 0 1) 0 2

def backward : Store Nat 3 := link (link threeSources 0 2) 0 1

/-- A key that records the dependency set and the content of each source in a
fixed source order, forgetting the dependency order. -/
def unorderedKey (point : Point) : Fin 3 × Nat × List Nat × List Bool × List (List Nat) :=
  (point.2, (point.1.members point.2).revision, (point.1.members point.2).own,
    (List.finRange 3).map fun source => decide (source ∈ (point.1.members point.2).deps),
    (List.finRange 3).map fun source => (point.1.members source).own)

def reorderedFiber : NonTrivialFiber unorderedKey answerOf where
  left := (forward, 0)
  right := (backward, 0)
  sameShadow := by decide
  differentValue := by decide

/-- **The dependency order belongs to the key.** The two answers are equal
bags. -/
theorem unordered_dependencies_not_key :
    (query forward 0).Perm (query backward 0) ∧ ¬ SoundKey unorderedKey answerOf :=
  ⟨by decide, fun sound => reorderedFiber.differentValue (sound _ _ reorderedFiber.sameShadow)⟩

/-! ### Negative lookups -/

/-- Reader zero also imports source one, whose list is empty. -/
def withEmptyImport : Store Nat 3 := link imported 0 1

/-- Consult only the sources that contributed an occurrence. -/
def contributing (live : RevisionEnvironment (Fin 3) (List Nat × List (Fin 3))) (reader : Fin 3) :
    List (Fin 3) :=
  reader :: (live.current reader).2.filter fun source => !(live.current source).1.isEmpty

/-- **A dependency set made of contributing sources misses an absence**: an
insertion into the empty source changes the answer without touching any
consulted store. -/
theorem contributing_sources_miss_absence :
    ¬ ReadsDetermine (composed (Entry := Nat) (size := 3)) contributing := by
  apply not_readsDetermine_of_hidden (captured := contents withEmptyImport)
    (live := contents (appendOwn withEmptyImport 1 [8])) (query := 0)
  · unfold RevisionEnvironment.AgreesOn
    decide
  · decide

/-- Positive: the store's own stamp rejects the stale absence. -/
theorem stamp_rejects_stale_absence :
    composed (contents withEmptyImport) 0 = [42, 7, 7] ∧
      composed (contents (appendOwn withEmptyImport 1 [8])) 0 = [42, 7, 7, 8] ∧
      checkRead (appendOwn withEmptyImport 1 [8]) (readStamp withEmptyImport 0) = false := by
  decide

/-! ### Reverse notification -/

/-- A content update that advances only the writer's revision. -/
def writerOnlyUpdate (s : Store Nat 3) (writer : Fin 3) (contents : List Nat) : Store Nat 3 :=
  { s with
    members := fun reader =>
      let old := s.members reader
      { old with
        own := if reader = writer then contents else old.own
        revision := if reader = writer then old.revision + 1 else old.revision }
    epoch := s.epoch + 1 }

def writerOnlyStep (s : Store Nat 3) : Action Nat 3 → Store Nat 3
  | .append writer suffix => writerOnlyUpdate s writer ((s.members writer).own ++ suffix)
  | action => OrderedDependencyStore.step s action

/-- **Without the reverse notification the read stamp is not maintained.** -/
theorem writer_only_update_does_not_notify :
    ¬ Notifies writerOnlyStep ObserverInvariant (fun s reader => (s.members reader).revision)
      (fun s reader => view s reader) := by
  intro notifying
  have stale := notifying.notifies imported (.append 2 [8]) 0 imported_observers (by decide)
  revert stale
  decide

/-! ### Prefix-valid against fully current -/

/-- **A prefix certificate does not certify the full list.** -/
theorem prefix_does_not_certify_full :
    ¬ Certifies (OrderedDependencyStore.step (Entry := Nat) (size := 3)) (fun _ => True)
      (fun s => prefixStamp s 2) (fun stamp s => checkPrefix s stamp)
      (fun _ s => (s.members 2).own) := by
  intro certified
  have kept := certified imported [.append 2 [8]] trivial (by decide)
  revert kept
  decide

/-- An append keeps the certified occurrence and invalidates an absence. -/
theorem append_keeps_occurrence_breaks_absence :
    checkPrefix (appendOwn imported 2 [8]) (prefixStamp imported 2) = true ∧
      resolvePrefix (appendOwn imported 2 [8]) (prefixStamp imported 2) 0 = some 7 ∧
      (8 ∉ (imported.members 2).own) ∧ (8 ∈ ((appendOwn imported 2 [8]).members 2).own) := by
  decide

/-! ### A key is not a read window -/

/-- Replace the reader's own list, then append to its dependency. -/
def tornRun : List (Action Nat 3) := [.replace 0 [43], .append 2 [8]]

/-- Part zero is read at time zero, part one at time two. -/
def tornTimes : Nat → Nat
  | 0 => 0
  | _ => 2

/-- **One key check at the opening does not make a read current**: the
assembled answer is the answer of no state of the run. -/
theorem torn_read_after_single_check :
    readStamp (runAt OrderedDependencyStore.step imported tornRun 0) 0 = readStamp imported 0 ∧
      assemble (Notifies.windowRead OrderedDependencyStore.step imported tornRun part 0 tornTimes) 2 =
        [42, 7, 7, 8] ∧
      ∀ time ≤ 2, query (runAt OrderedDependencyStore.step imported tornRun time) 0 ≠
        [42, 7, 7, 8] := by
  decide

/-- An append to the reader's own list. -/
def ownAppend : List (Action Nat 3) := [.append 0 [5]]

/-- Part zero is read before the opening check at time one. -/
def reorderedTimes : Nat → Nat
  | 0 => 0
  | _ => 1

/-- **Two agreeing checks do not help a read placed outside the window**: the
answer is superseded at the certified time. -/
theorem reordered_read_after_double_check :
    readStamp (runAt OrderedDependencyStore.step imported ownAppend 1) 0 =
        readStamp (runAt OrderedDependencyStore.step imported ownAppend 1) 0 ∧
      assemble (Notifies.windowRead OrderedDependencyStore.step imported ownAppend part 0 reorderedTimes) 2 =
        [42, 7, 7] ∧
      query (runAt OrderedDependencyStore.step imported ownAppend 1) 0 = [42, 5, 7, 7] := by
  decide

/-- An unrelated append. -/
def unrelatedAppend : List (Action Nat 3) := [.append 1 [9]]

def spreadTimes : Nat → Nat
  | 0 => 0
  | _ => 1

/-- **Positive: reads spread across a window with agreeing keys assemble the
answer at the opening.** -/
theorem windowed_read_is_current :
    assemble (Notifies.windowRead OrderedDependencyStore.step imported unrelatedAppend part 0 spreadTimes) 2 =
      query imported 0 := by
  have parts := store_notifies_parts.windowRead_eq imported_observers unrelatedAppend
    (opening := 0) (closing := 1) (0 : Fin 3) (by decide) spreadTimes 2
    (fun index _ => by cases index <;> simp [spreadTimes])
  have congruent : (List.range 2).filterMap
      (Notifies.windowRead OrderedDependencyStore.step imported unrelatedAppend part 0 spreadTimes) =
      (List.range 2).filterMap (part imported 0) := by
    apply List.filterMap_congr
    intro index member
    exact parts index (List.mem_range.mp member)
  unfold assemble
  rw [congruent]
  decide

/-! ### Owner lifetime is not currency -/

def lifetimeKey (point : Point) : Nat × Fin 3 × Nat :=
  (point.1.identity, point.2, (point.1.members point.2).generation)

def liveOwnerFiber : NonTrivialFiber lifetimeKey answerOf where
  left := (imported, 0)
  right := (appendOwn imported 2 [8], 0)
  sameShadow := by decide
  differentValue := by decide

/-- **A live owner does not make an answer current.** -/
theorem lifetime_key_not_currency : ¬ SoundKey lifetimeKey answerOf :=
  fun sound => liveOwnerFiber.differentValue (sound _ _ liveOwnerFiber.sameShadow)

end Controls

#print axioms store_notifies
#print axioms readStamp_soundKey_run
#print axioms readStamp_soundKey_sessions
#print axioms prefix_certifies_prefix
#print axioms composed_determined
#print axioms contentKey_sound
#print axioms projectionStamp_soundKey_run
#print axioms overlayStamp_soundKey_run
#print axioms store_notifies_parts
#print axioms Controls.revision_alone_not_key
#print axioms Controls.epoch_alone_not_key
#print axioms Controls.imported_run_sound
#print axioms Controls.identity_reuse_not_key
#print axioms Controls.distinct_identities_sound
#print axioms Controls.slot_free_stamp_not_key
#print axioms Controls.overlay_change_not_key
#print axioms Controls.overlay_stamp_rejects_publication
#print axioms Controls.unordered_dependencies_not_key
#print axioms Controls.contributing_sources_miss_absence
#print axioms Controls.stamp_rejects_stale_absence
#print axioms Controls.writer_only_update_does_not_notify
#print axioms Controls.prefix_does_not_certify_full
#print axioms Controls.append_keeps_occurrence_breaks_absence
#print axioms Controls.torn_read_after_single_check
#print axioms Controls.reordered_read_after_double_check
#print axioms Controls.windowed_read_is_current
#print axioms Controls.lifetime_key_not_currency

end Mettapedia.Machines.OrderedDependencyCacheKeys
