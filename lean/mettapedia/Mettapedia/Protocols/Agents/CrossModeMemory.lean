import Mettapedia.Protocols.Agents.RuntimeMaintenance

/-!
# Cross-mode memory

A history belongs to an agent and a history lineage. A mode supplies the
origin of a record and interprets the captured history on entry. The same
contract permits full reads, maintained exact views, and paging. Delivery
settlement still needs the captured input frame of `ResumableModeCheckpoint`.

Publication below is a transition on the committed record. The runtime must
establish its durability before acknowledging anyone. Ownership transfer
retains pending work and grants no permission to repeat an uncertain effect.
-/

set_option autoImplicit false

namespace Mettapedia.Protocols.Agents.CrossModeMemory

universe u
variable {Scope Id Mode Payload Row Work : Type u}

structure Occurrence (Id Mode Payload : Type u) where
  id : Id
  origin : Mode
  body : Payload
  deriving DecidableEq, Repr

structure Lease (Mode : Type u) where
  mode : Mode
  epoch : Nat
  deriving DecidableEq, Repr

/-- A durable handoff retains each unresolved obligation with its evidence. -/
structure Boundary (Mode Row Work : Type u) where
  owner : Lease Mode
  history : List Row
  pending : List Work

def handoff (s : Boundary Mode Row Work) (next : Mode) : Boundary Mode Row Work :=
  { s with owner := ⟨next, s.owner.epoch + 1⟩ }

def drainThenSwitch (s : Boundary Mode Row Work) (next : Mode) :
    Option (Boundary Mode Row Work) :=
  if s.pending.isEmpty then some (handoff s next) else none

theorem handoff_preserves_records (s : Boundary Mode Row Work) (next : Mode) :
    (handoff s next).history = s.history ∧ (handoff s next).pending = s.pending :=
  ⟨rfl, rfl⟩

theorem drain_switch_agrees_at_boundary (s : Boundary Mode Row Work) (next : Mode)
    (h : s.pending = []) : drainThenSwitch s next = some (handoff s next) := by
  simp [drainThenSwitch, h]

theorem unresolved_work_prevents_drain (s : Boundary Mode Row Work) (next : Mode)
    (h : s.pending ≠ []) : drainThenSwitch s next = none := by
  simp [drainThenSwitch, List.isEmpty_iff, h]

theorem handoff_invalidates_lease (s : Boundary Mode Row Work) (next : Mode) :
    (handoff s next).owner ≠ s.owner := by
  intro h
  have epoch := congrArg Lease.epoch h
  change s.owner.epoch + 1 = s.owner.epoch at epoch
  omega

def lookup [DecidableEq Id] (id : Id) (rows : List (Occurrence Id Mode Payload)) :
    Option (Occurrence Id Mode Payload) :=
  rows.find? (fun row => decide (row.id = id))

theorem lookup_absent [DecidableEq Id] (id : Id) (rows : List (Occurrence Id Mode Payload)) :
    lookup id rows = none ↔ id ∉ rows.map Occurrence.id := by
  simp [lookup, List.find?_eq_none, List.mem_map]

inductive Publication (Row : Type u) where
  | appended (history : List Row)
  | replayed
  | conflict
  | staleOwner
  deriving DecidableEq, Repr

def publish [DecidableEq Id] [DecidableEq Mode] [DecidableEq Payload]
    (owner caller : Lease Mode) (rows : List (Occurrence Id Mode Payload))
    (row : Occurrence Id Mode Payload) : Publication (Occurrence Id Mode Payload) :=
  if caller ≠ owner then .staleOwner else
    match lookup row.id rows with
    | none => .appended (rows ++ [row])
    | some old => if old = row then .replayed else .conflict

theorem publication_is_exact [DecidableEq Id] [DecidableEq Mode] [DecidableEq Payload]
    {owner caller : Lease Mode} {rows next : List (Occurrence Id Mode Payload)}
    {row : Occurrence Id Mode Payload} (h : publish owner caller rows row = .appended next) :
    caller = owner ∧ row.id ∉ rows.map Occurrence.id ∧ next = rows ++ [row] := by
  unfold publish at h
  split at h
  · contradiction
  · next current =>
    split at h
    · next missing =>
      cases h
      exact ⟨Decidable.byContradiction current, (lookup_absent _ _).mp missing, rfl⟩
    · split at h <;> contradiction

theorem publication_preserves_unique_ids [DecidableEq Id] [DecidableEq Mode]
    [DecidableEq Payload] {owner caller : Lease Mode}
    {rows next : List (Occurrence Id Mode Payload)} {row : Occurrence Id Mode Payload}
    (unique : (rows.map Occurrence.id).Nodup)
    (h : publish owner caller rows row = .appended next) :
    (next.map Occurrence.id).Nodup := by
  obtain ⟨_, fresh, rfl⟩ := publication_is_exact h
  have unmatched (old : Occurrence Id Mode Payload) (member : old ∈ rows) :
      old.id ≠ row.id :=
    fun equal => fresh (List.mem_map.mpr ⟨old, member, equal⟩)
  simpa [List.nodup_append, unique] using unmatched

theorem accepted_append_has_receipt [DecidableEq Id] [DecidableEq Mode]
    [DecidableEq Payload] {owner caller : Lease Mode}
    {rows next : List (Occurrence Id Mode Payload)} {row : Occurrence Id Mode Payload}
    (h : publish owner caller rows row = .appended next) :
    lookup row.id next = some row := by
  obtain ⟨_, fresh, rfl⟩ := publication_is_exact h
  have noneBefore := (lookup_absent row.id rows).mpr fresh
  unfold lookup at noneBefore ⊢
  rw [List.find?_append, noneBefore]
  simp

theorem lost_reply_replays_by_id [DecidableEq Id] [DecidableEq Mode] [DecidableEq Payload]
    {owner : Lease Mode} {rows next : List (Occurrence Id Mode Payload)}
    {row : Occurrence Id Mode Payload}
    (h : publish owner owner rows row = .appended next) :
    publish owner owner next row = .replayed := by
  simp [publish, accepted_append_has_receipt h]

theorem stale_mode_cannot_publish [DecidableEq Id] [DecidableEq Mode] [DecidableEq Payload]
    (s : Boundary Mode (Occurrence Id Mode Payload) Work) (mode : Mode)
    (row : Occurrence Id Mode Payload) :
    publish (handoff s mode).owner s.owner (handoff s mode).history row = .staleOwner := by
  simp [publish, Ne.symm (handoff_invalidates_lease s mode)]

/-- The memory-relevant part of a run. A failed attempt publishes no row.
The handoff step assumes its pending obligations are already durable. -/
inductive Step [DecidableEq Id] [DecidableEq Mode] [DecidableEq Payload] :
    Boundary Mode (Occurrence Id Mode Payload) Work →
    Boundary Mode (Occurrence Id Mode Payload) Work → Prop
  | transfer (s : Boundary Mode (Occurrence Id Mode Payload) Work) (mode : Mode) :
      Step s (handoff s mode)
  | append (s : Boundary Mode (Occurrence Id Mode Payload) Work)
      (caller : Lease Mode) (row : Occurrence Id Mode Payload) (next : List (Occurrence Id Mode Payload))
      (accepted : publish s.owner caller s.history row = .appended next) :
      Step s {s with history := next}

inductive Run [DecidableEq Id] [DecidableEq Mode] [DecidableEq Payload]
    (initial : Boundary Mode (Occurrence Id Mode Payload) Work) :
    Boundary Mode (Occurrence Id Mode Payload) Work → Prop
  | start : Run initial initial
  | step {prior next : Boundary Mode (Occurrence Id Mode Payload) Work}
      (run : Run initial prior) (transition : Step prior next) : Run initial next

theorem run_extends_history [DecidableEq Id] [DecidableEq Mode] [DecidableEq Payload]
    {initial final : Boundary Mode (Occurrence Id Mode Payload) Work} (run : Run initial final) :
    ∃ added, final.history = initial.history ++ added := by
  induction run with
  | start => exact ⟨[], (List.append_nil _).symm⟩
  | step _ transition ih =>
    obtain ⟨added, history⟩ := ih
    cases transition with
    | transfer _ => exact ⟨added, history⟩
    | append _ row _ accepted =>
      obtain ⟨_, _, rfl⟩ := publication_is_exact accepted
      exact ⟨added ++ [row], by simp only [history, List.append_assoc]⟩

/-! ## Entry, catch-up and exact paging -/

structure Snapshot (Scope Row : Type u) where
  scope : Scope
  rows : List Row
  deriving DecidableEq, Repr

structure Cursor (Scope : Type u) where
  scope : Scope
  offset : Nat

def since [DecidableEq Scope] (cursor : Cursor Scope) (snapshot : Snapshot Scope Row) :
    Option (List Row) :=
  if cursor.scope = snapshot.scope ∧ cursor.offset ≤ snapshot.rows.length then
    some (snapshot.rows.drop cursor.offset)
  else none

theorem reentry_covers_intervening_records [DecidableEq Scope] (scope : Scope)
    (seen intervening : List Row) :
    since ⟨scope, seen.length⟩ ⟨scope, seen ++ intervening⟩ = some intervening := by
  simp [since]

theorem reentry_after_any_run [DecidableEq Scope] [DecidableEq Id] [DecidableEq Mode]
    [DecidableEq Payload] (scope : Scope)
    {initial final : Boundary Mode (Occurrence Id Mode Payload) Work} (run : Run initial final) :
    ∃ added, final.history = initial.history ++ added ∧
      since ⟨scope, initial.history.length⟩ ⟨scope, final.history⟩ = some added := by
  obtain ⟨added, history⟩ := run_extends_history run
  refine ⟨added, history, ?_⟩
  rw [history]
  exact reentry_covers_intervening_records scope _ _

theorem entry_rejects_different_lineage [DecidableEq Scope] (cursor : Cursor Scope)
    (snapshot : Snapshot Scope Row) (h : cursor.scope ≠ snapshot.scope) :
    since cursor snapshot = none := by
  simp [since, h]

theorem entry_rejects_future_cursor [DecidableEq Scope] (cursor : Cursor Scope)
    (snapshot : Snapshot Scope Row) (h : snapshot.rows.length < cursor.offset) :
    since cursor snapshot = none := by
  simp [since, Nat.not_le_of_lt h]

/-- A cached prefix can be extended only after its identity and order agree. -/
def refresh [DecidableEq Scope] [DecidableEq Row] (cached captured : Snapshot Scope Row) :
    Option (Snapshot Scope Row) :=
  if cached.scope = captured.scope then
    (RuntimeMaintenance.membershipDelta cached.rows captured.rows).map
      (fun delta => ⟨cached.scope, cached.rows ++ delta⟩)
  else none

theorem refresh_equals_full_read [DecidableEq Scope] [DecidableEq Row]
    {cached captured next : Snapshot Scope Row} (h : refresh cached captured = some next) :
    next = captured := by
  unfold refresh at h
  split at h
  · next scope =>
    cases delta : RuntimeMaintenance.membershipDelta cached.rows captured.rows with
    | none => simp [delta] at h
    | some added =>
      simp only [delta, Option.map_some, Option.some.injEq] at h
      rw [← h, scope, RuntimeMaintenance.membership_delta_preserves_prefix delta]
  · contradiction

theorem refresh_after_append [DecidableEq Scope] [DecidableEq Row]
    (scope : Scope) (old added : List Row) :
    refresh ⟨scope, old⟩ ⟨scope, old ++ added⟩ = some ⟨scope, old ++ added⟩ := by
  simp [refresh, RuntimeMaintenance.membershipDelta]

def page (snapshot : Snapshot Scope Row) (start through : Nat) : Option (List Row) :=
  if start ≤ through ∧ through ≤ snapshot.rows.length then
    some ((snapshot.rows.take through).drop start)
  else none

theorem earlier_page_survives_append (scope : Scope) (old added : List Row)
    (start through : Nat) (h : through ≤ old.length) :
    page ⟨scope, old ++ added⟩ start through = page ⟨scope, old⟩ start through := by
  have longer : through ≤ old.length + added.length := by omega
  simp [page, h, longer, List.take_append_of_le_length h]

theorem full_history_from_prefix_and_tail (snapshot : Snapshot Scope Row) (cut : Nat) :
    snapshot.rows.take cut ++ snapshot.rows.drop cut = snapshot.rows :=
  List.take_append_drop _ _

/-! ## Recovery of a refused projection -/

inductive RecoveryEvidence (Row : Type u) where
  | original (row : Row)
  | summary
  | unknown
  deriving DecidableEq

inductive Recovery (Row : Type u) where
  | append (row : Row)
  | alreadyRecorded
  | conflict
  | pending
  deriving DecidableEq

/-- Discovery needs a complete observation through the captured frontier.
`publish` then checks the live owner and occurrence ID before a write. -/
def recover [DecidableEq Scope] [DecidableEq Id] [DecidableEq Mode] [DecidableEq Payload]
    (scope : Scope) (id : Id) (observed : Option (Snapshot Scope (Occurrence Id Mode Payload)))
    (evidence : RecoveryEvidence (Occurrence Id Mode Payload)) :
    Recovery (Occurrence Id Mode Payload) :=
  match observed, evidence with
  | some current, .original record =>
    if current.scope ≠ scope ∨ record.id ≠ id then .conflict else
      match lookup id current.rows with
      | none => .append record
      | some old => if old = record then .alreadyRecorded else .conflict
  | _, _ => .pending

theorem unavailable_stays_pending [DecidableEq Scope] [DecidableEq Id] [DecidableEq Mode]
    [DecidableEq Payload] (scope : Scope) (id : Id)
    (evidence : RecoveryEvidence (Occurrence Id Mode Payload)) :
    recover scope id none evidence = .pending := by
  cases evidence <;> rfl

theorem summary_cannot_recover_original [DecidableEq Scope] [DecidableEq Id] [DecidableEq Mode]
    [DecidableEq Payload] (scope : Scope) (id : Id)
    (observed : Option (Snapshot Scope (Occurrence Id Mode Payload))) :
    recover scope id observed .summary = .pending := by
  cases observed <;> rfl

theorem repair_already_committed [DecidableEq Scope] [DecidableEq Id] [DecidableEq Mode]
    [DecidableEq Payload] (scope : Scope) {owner : Lease Mode}
    {rows next : List (Occurrence Id Mode Payload)} {row : Occurrence Id Mode Payload}
    (h : publish owner owner rows row = .appended next) :
    recover scope row.id (some ⟨scope, next⟩) (.original row) = .alreadyRecorded := by
  have receipt := accepted_append_has_receipt h
  simp [recover, receipt]

theorem recovery_collision_is_explicit [DecidableEq Scope] [DecidableEq Id] [DecidableEq Mode]
    [DecidableEq Payload] (scope : Scope) (rows : List (Occurrence Id Mode Payload))
    (old offered : Occurrence Id Mode Payload) (h : lookup offered.id rows = some old)
    (conflict : old ≠ offered) :
    recover scope offered.id (some ⟨scope, rows⟩) (.original offered) = .conflict := by
  simp [recover, h, conflict]

theorem recovery_requires_original_and_observed_miss [DecidableEq Scope] [DecidableEq Id]
    [DecidableEq Mode] [DecidableEq Payload] {scope : Scope} {id : Id}
    {observed : Option (Snapshot Scope (Occurrence Id Mode Payload))}
    {evidence : RecoveryEvidence (Occurrence Id Mode Payload)}
    {row : Occurrence Id Mode Payload} (h : recover scope id observed evidence = .append row) :
    evidence = .original row ∧ ∃ captured, observed = some captured ∧
      captured.scope = scope ∧ row.id = id ∧ lookup id captured.rows = none := by
  cases observed with
  | none => simp [unavailable_stays_pending] at h
  | some captured =>
    cases evidence with
    | summary => cases h
    | unknown => cases h
    | original record =>
      by_cases rejected : captured.scope ≠ scope ∨ record.id ≠ id
      · simp [recover, rejected] at h
      · cases found : lookup id captured.rows with
        | none =>
          simp only [recover, if_neg rejected, found, Recovery.append.injEq] at h
          subst record
          refine ⟨rfl, captured, rfl, ?_, ?_, found⟩
          · exact Decidable.byContradiction (fun wrong => rejected (Or.inl wrong))
          · exact Decidable.byContradiction (fun wrong => rejected (Or.inr wrong))
        | some old =>
          simp only [recover, if_neg rejected, found] at h
          split at h <;> contradiction

/-- Regenerate a derived occurrence under a new, source-addressed identity.
The recipe supplies a payload only when the retained evidence suffices. Its
identity can name a version and output position. -/
def rebuildProjection {Recipe Body : Type u} [DecidableEq Scope] [DecidableEq Id]
    (source : Snapshot Scope (Occurrence Id Mode Payload)) (scope : Scope)
    (id : Id) (recipe : Recipe) (project : Occurrence Id Mode Payload → Option Body) :
    Option (Occurrence (Id × Recipe) Mode Body) :=
  if source.scope ≠ scope then none else
    (lookup id source.rows).bind (fun row =>
      (project row).map (fun body => ⟨(row.id, recipe), row.origin, body⟩))

theorem rebuilt_projection_has_source {Recipe Body : Type u} [DecidableEq Scope] [DecidableEq Id]
    {source : Snapshot Scope (Occurrence Id Mode Payload)} {scope : Scope} {id : Id}
    {recipe : Recipe} {project : Occurrence Id Mode Payload → Option Body}
    {rebuilt : Occurrence (Id × Recipe) Mode Body}
    (h : rebuildProjection source scope id recipe project = some rebuilt) :
    source.scope = scope ∧ ∃ row, lookup id source.rows = some row ∧
      project row = some rebuilt.body ∧ rebuilt.id = (row.id, recipe) ∧
      rebuilt.origin = row.origin := by
  unfold rebuildProjection at h
  split at h
  · contradiction
  · next same =>
    cases found : lookup id source.rows with
    | none => simp [found] at h
    | some row =>
      cases built : project row with
      | none => simp [found, built] at h
      | some body =>
        simp only [found, built, Option.bind_some, Option.map_some, Option.some.injEq] at h
        subst rebuilt
        exact ⟨Decidable.byContradiction same, row, rfl, built, rfl, rfl⟩

/-! ## Discriminating traces -/

private def first : Occurrence Nat String String := ⟨1, "Iter", "ok"⟩
private def other : Occurrence Nat String String := ⟨2, "Omega", "ok"⟩
private def owner : Lease String := ⟨"Omega", 4⟩

theorem equal_payloads_have_distinct_occurrences :
    publish owner owner [first] other = .appended [first, other] := by decide

theorem mode_private_history_misses_intervening_turn :
    since (⟨"agent", 1⟩ : Cursor String) ⟨"agent", [first, other]⟩ = some [other] ∧
    since (⟨"agent", 1⟩ : Cursor String) ⟨"agent", [first]⟩ = some [] := by decide

theorem equal_counts_do_not_validate_a_cached_view :
    refresh (⟨"agent", [first, other]⟩ : Snapshot String _) ⟨"agent", [other, first]⟩ =
      none := by decide

theorem identical_contents_cannot_cross_agent_scope :
    refresh (⟨"agent-a", [first]⟩ : Snapshot String _) ⟨"agent-b", [first]⟩ = none := by decide

theorem capped_suffix_cannot_reconstruct_history (keep : Nat) :
    ¬ ∃ restore : List Nat → List Nat, ∀ rows : List Nat,
      restore (rows.drop (rows.length - keep)) = rows := by
  intro ⟨restore, all⟩
  let suffix := List.replicate keep 9
  have left : restore suffix = 1 :: suffix := by
    simpa [suffix] using all (1 :: suffix)
  have right : restore suffix = 2 :: suffix := by
    simpa [suffix] using all (2 :: suffix)
  have impossible : (1 : Nat) = 2 := (List.cons.inj (left.symm.trans right)).1
  exact (by decide : (1 : Nat) ≠ 2) impossible

#print axioms publication_preserves_unique_ids
#print axioms lost_reply_replays_by_id
#print axioms stale_mode_cannot_publish
#print axioms reentry_covers_intervening_records
#print axioms reentry_after_any_run
#print axioms refresh_equals_full_read
#print axioms earlier_page_survives_append
#print axioms repair_already_committed
#print axioms recovery_requires_original_and_observed_miss
#print axioms rebuilt_projection_has_source
#print axioms capped_suffix_cannot_reconstruct_history

end Mettapedia.Protocols.Agents.CrossModeMemory
