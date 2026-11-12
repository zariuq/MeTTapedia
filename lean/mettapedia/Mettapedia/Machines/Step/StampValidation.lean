import Mettapedia.Machines.Cursor.StampedSnapshots
import Mettapedia.Machines.Step.Firing
import Mathlib.Data.List.Perm.Subperm
import Mathlib.Data.Multiset.Basic

/-!
# Validating a branch by the stamps of its rows

The store is the stamped store of `Cursor.StampedSnapshots`: rows keep their
slot, a removal writes a death stamp once, an addition takes the next slot.  A
branch is proposed against the store at one moment and fires at a later one,
after any additions and removals by anyone.  It names the rows it met (the
slots of its reads and of its takes), carries its `absent` predicate and its
outputs, and remembers one number from the moment of proposal: the store's
next free slot (`ceiling`).

Validation at the later moment compares stamps only:

* a **take** is valid when its row has no death stamp;
* a **read** is valid when its row has no death stamp (if reads are rechecked);
* an **absent** is valid when no row at or above the ceiling is live and
  satisfies the predicate.  Rows below the ceiling need no look: they were
  tested at proposal and a removal cannot make one match.

* `validate_sound`: a branch that validates is a firing of the store as it is
  at the later moment (`Firing.Enabled` of the multiset of live rows).
* `absent_now_iff`: for `absent` the test is exact, not conservative.
* `validate_sound_query`: when reads are not rechecked, the takes, the absent
  conditions and the outputs still are a firing of the later store; the reads
  were satisfied by the store at proposal.
* `Controls.snapshot_reads_or_current_firing`: the two readings cannot both be
  kept.  A reads-only branch whose row was removed after the proposal is an
  answer of the entry view and is not a firing of the store when it is
  delivered.  Answering as the entry view and delivering only current firings
  are incompatible once a consumer writes between answers.
* `count_valid_iff_rebinding`, `Controls.stamps_refuse_where_counts_accept`:
  validation by stamps is by occurrence, and is stricter than validation by
  counting copies: with two copies of an atom, a branch that met the first
  copy is refused by stamps once that copy is removed, though a copy is
  stored.  Counting accepts exactly when some other live rows with the same
  atoms can stand in.  A stamp test followed, on failure, by one search for
  another live copy therefore decides the count rule.
* `Controls.row_stamps_miss_an_added_row`: an `absent` cannot be validated from
  the rows of the footprint.  Its footprint holds no row; what must be watched
  is the part of the store added since the proposal.

Every test is a comparison of one stamp, so validation costs one comparison
for each take, one for each read that is rechecked, and one visit for each row
at or above the ceiling for each `absent` (or one search in an index of that
part).

`run_later` shows that every sequence of additions and removals satisfies the
hypotheses.  Not modelled: the reclamation of dead rows, ordered spaces (where
which copy is taken is observable), and stored atoms with variables.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Step.StampValidation

open Mettapedia.Machines.Cursor.StampedSnapshots

variable {α : Type}

/-- The row in a slot is live: it has no death stamp. -/
def Alive (s : Store α) (id : Nat) : Prop := ∃ r, s.row id = some r ∧ r.death = none

/-- The stamp test for liveness. -/
def aliveB (s : Store α) (id : Nat) : Bool :=
  match s.row id with
  | some r => r.death.isNone
  | none => false

theorem aliveB_iff (s : Store α) (id : Nat) : aliveB s id = true ↔ Alive s id := by
  unfold aliveB Alive
  cases h : s.row id with
  | none => simp
  | some r => simp [Option.isNone_iff_eq_none]

/-- The atom in a slot. -/
def valueOf (s : Store α) (id : Nat) : Option α := (s.row id).map Row.value

/-- The shape every store reached by additions and removals has. -/
structure WF (s : Store α) : Prop where
  beyond : ∀ id, s.next ≤ id → s.row id = none
  filled : ∀ id, id < s.next → ∃ r, s.row id = some r

theorem wf_empty : WF (empty : Store α) :=
  ⟨fun _ _ => rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩

theorem add_row (s : Store α) (v : α) (id : Nat) :
    (add s v).row id = if id = s.next then some ⟨v, s.clock + 1, none⟩ else s.row id := by
  simp [add, Function.update_apply]

/-- A removal changes nothing, or stamps one live row. -/
theorem remove_cases (s : Store α) (gone : Nat) :
    remove s gone = s ∨
      ∃ r, s.row gone = some r ∧ r.death = none ∧ (remove s gone).next = s.next ∧
        ∀ id, (remove s gone).row id =
          if id = gone then some { r with death := some (s.clock + 1) } else s.row id := by
  unfold remove
  cases h : s.row gone with
  | none => exact Or.inl rfl
  | some r =>
    cases hd : r.death with
    | some d => exact Or.inl (by simp [hd])
    | none =>
      refine Or.inr ⟨r, rfl, hd, ?_, fun id => ?_⟩
      · simp [hd]
      · simp [hd, Function.update_apply]

theorem WF.add {s : Store α} (wf : WF s) (v : α) : WF (add s v) := by
  refine ⟨fun id h => ?_, fun id h => ?_⟩
  · have h' : s.next + 1 ≤ id := h
    rw [add_row, if_neg (by omega)]
    exact wf.beyond id (by omega)
  · have h' : id < s.next + 1 := h
    rw [add_row]
    by_cases eq : id = s.next
    · exact ⟨_, if_pos eq⟩
    · rw [if_neg eq]
      exact wf.filled id (by omega)

theorem WF.remove {s : Store α} (wf : WF s) (gone : Nat) : WF (remove s gone) := by
  rcases remove_cases s gone with same | ⟨r, found, _, next, rows⟩
  · rw [same]
    exact wf
  · refine ⟨fun id h => ?_, fun id h => ?_⟩
    · rw [next] at h
      rw [rows]
      by_cases eq : id = gone
      · subst eq
        rw [wf.beyond id h] at found
        cases found
      · rw [if_neg eq]
        exact wf.beyond id h
    · rw [next] at h
      rw [rows]
      by_cases eq : id = gone
      · exact ⟨_, if_pos eq⟩
      · rw [if_neg eq]
        exact wf.filled id h

/-- What a later store keeps of an earlier one: its slots, with their atoms,
and no dead row alive again. -/
structure Later (s0 s1 : Store α) : Prop where
  next : s0.next ≤ s1.next
  old : ∀ id r0, s0.row id = some r0 →
    ∃ r1, s1.row id = some r1 ∧ r1.value = r0.value ∧ (r1.death = none → r0.death = none)

theorem Later.refl (s : Store α) : Later s s :=
  ⟨le_rfl, fun _ r0 h => ⟨r0, h, rfl, id⟩⟩

theorem Later.add {s0 s1 : Store α} (wf0 : WF s0) (later : Later s0 s1) (v : α) :
    Later s0 (add s1 v) := by
  refine ⟨later.next.trans (Nat.le_succ _), fun id r0 h => ?_⟩
  have below : id < s0.next := by
    by_contra not
    rw [wf0.beyond id (by omega)] at h
    cases h
  have := later.next
  rw [add_row, if_neg (by omega)]
  exact later.old id r0 h

theorem Later.remove {s0 s1 : Store α} (later : Later s0 s1) (gone : Nat) :
    Later s0 (remove s1 gone) := by
  rcases remove_cases s1 gone with same | ⟨r, found, _, next, rows⟩
  · rw [same]
    exact later
  · refine ⟨next ▸ later.next, fun id r0 h => ?_⟩
    obtain ⟨r1, h1, val, live⟩ := later.old id r0 h
    rw [rows]
    by_cases eq : id = gone
    · subst eq
      rw [found] at h1
      cases h1
      exact ⟨_, if_pos rfl, val, fun dead => by cases dead⟩
    · exact ⟨r1, by rw [if_neg eq]; exact h1, val, live⟩

/-- One write by anyone. -/
inductive Write (α : Type) where
  | add (value : α)
  | remove (id : Nat)

def Write.apply : Write α → Store α → Store α
  | .add v, s => Cursor.StampedSnapshots.add s v
  | .remove id, s => Cursor.StampedSnapshots.remove s id

/-- A sequence of writes. -/
def run (ws : List (Write α)) (s : Store α) : Store α := ws.foldl (fun s w => w.apply s) s

/-- **Every sequence of additions and removals** leaves a well-formed store
that is later than the one it started from. -/
theorem run_later {s0 : Store α} (wf0 : WF s0) (ws : List (Write α)) :
    WF (run ws s0) ∧ Later s0 (run ws s0) := by
  suffices h : ∀ s1, WF s1 → Later s0 s1 → WF (run ws s1) ∧ Later s0 (run ws s1) from
    h s0 wf0 (Later.refl s0)
  induction ws with
  | nil => exact fun s1 wf later => ⟨wf, later⟩
  | cons w ws ih =>
    intro s1 wf later
    cases w with
    | add v => exact ih (Cursor.StampedSnapshots.add s1 v) (wf.add v) (later.add wf0 v)
    | remove id => exact ih (Cursor.StampedSnapshots.remove s1 id) (wf.remove id) (later.remove id)

/-- The slots of the live rows. -/
def liveIds (s : Store α) : List Nat := (List.range s.next).filter (aliveB s)

/-- The store's content now: the atoms of its live rows. -/
def live (s : Store α) : Multiset α := ((liveIds s).filterMap (valueOf s) : List α)

theorem mem_liveIds {s : Store α} (wf : WF s) (id : Nat) : id ∈ liveIds s ↔ Alive s id := by
  unfold liveIds
  rw [List.mem_filter, List.mem_range, aliveB_iff]
  constructor
  · exact fun h => h.2
  · rintro ⟨r, found, dead⟩
    refine ⟨?_, r, found, dead⟩
    by_contra not
    rw [wf.beyond id (by omega)] at found
    cases found

theorem mem_live {s : Store α} (wf : WF s) (a : α) :
    a ∈ live s ↔ ∃ id r, s.row id = some r ∧ r.death = none ∧ r.value = a := by
  unfold live
  rw [Multiset.mem_coe, List.mem_filterMap]
  constructor
  · rintro ⟨id, mem, val⟩
    obtain ⟨r, found, dead⟩ := (mem_liveIds wf id).mp mem
    refine ⟨id, r, found, dead, ?_⟩
    simpa [valueOf, found] using val
  · rintro ⟨id, r, found, dead, rfl⟩
    exact ⟨id, (mem_liveIds wf id).mpr ⟨r, found, dead⟩, by simp [valueOf, found]⟩

/-- Distinct live rows are a part of the store's content. -/
theorem vals_le_live {s : Store α} (wf : WF s) (ids : List Nat) (nodup : ids.Nodup)
    (alive : ∀ id ∈ ids, Alive s id) :
    ((ids.filterMap (valueOf s) : List α) : Multiset α) ≤ live s := by
  have sub : ids ⊆ liveIds s := fun id mem => (mem_liveIds wf id).mpr (alive id mem)
  obtain ⟨l, perm, sublist⟩ := List.subperm_of_subset nodup sub
  exact Multiset.coe_le.mpr ⟨l.filterMap (valueOf s), perm.filterMap _, sublist.filterMap _⟩

/-- A branch: the rows it met, its `absent` predicate, its outputs, and the
store's next free slot when it was proposed. -/
structure Branch (α : Type) where
  reads : List Nat
  takes : List Nat
  absent : α → Prop
  outputs : Multiset α
  ceiling : Nat

/-- No live row satisfies the predicate. -/
def AbsentHolds (s : Store α) (p : α → Prop) : Prop :=
  ∀ id r, s.row id = some r → r.death = none → ¬ p r.value

/-- The stamp test for an `absent`: no live row at or above the ceiling
satisfies the predicate. -/
def NoNewMatch (s : Store α) (br : Branch α) : Prop :=
  ∀ id r, br.ceiling ≤ id → s.row id = some r → r.death = none → ¬ br.absent r.value

/-- **For `absent` the stamp test is exact.**  If the predicate held of no live
row at proposal, it holds of none now exactly when it holds of no live row at
or above the ceiling. -/
theorem absent_now_iff {s0 s1 : Store α} (wf0 : WF s0) (later : Later s0 s1) (br : Branch α)
    (ceiling : br.ceiling = s0.next) (held : AbsentHolds s0 br.absent) :
    AbsentHolds s1 br.absent ↔ NoNewMatch s1 br := by
  constructor
  · exact fun now id r _ found dead => now id r found dead
  · intro fresh id r found dead
    by_cases above : br.ceiling ≤ id
    · exact fresh id r above found dead
    · obtain ⟨r0, found0⟩ := wf0.filled id (by omega)
      obtain ⟨r1, found1, val, live⟩ := later.old id r0 found0
      rw [found] at found1
      cases found1
      rw [val]
      exact held id r0 found0 (live dead)

/-- **Counting copies is validation by stamps up to a choice of rows.**  The
atoms of a list of rows are stored now exactly when some distinct live rows
hold the same atoms. -/
theorem count_valid_iff_rebinding {s : Store α} (wf : WF s) (ids : List Nat) :
    ((ids.filterMap (valueOf s) : List α) : Multiset α) ≤ live s ↔
      ∃ ids' : List Nat, ids'.Nodup ∧ (∀ id ∈ ids', Alive s id) ∧
        (ids'.filterMap (valueOf s)).Perm (ids.filterMap (valueOf s)) := by
  constructor
  · intro le
    obtain ⟨l, perm, sublist⟩ := Multiset.coe_le.mp le
    obtain ⟨ids', sub, eq⟩ := List.sublist_filterMap_iff.mp sublist
    refine ⟨ids', ?_, fun id mem => ?_, eq ▸ perm⟩
    · exact (sub.nodup ((List.nodup_range).filter _))
    · exact (mem_liveIds wf id).mp (sub.subset mem)
  · rintro ⟨ids', nodup, alive, perm⟩
    rw [← Multiset.coe_eq_coe.mpr perm]
    exact vals_le_live wf ids' nodup alive

variable [DecidableEq α]

/-- The firing a branch stands for in a store: the atoms in its rows. -/
def firing (s : Store α) (br : Branch α) : Firing α where
  reads := (br.reads.filterMap (valueOf s) : List α)
  takes := (br.takes.filterMap (valueOf s) : List α)
  absent := br.absent
  outputs := br.outputs

/-- A branch whose take rows are distinct and live, whose read rows are live
and are not take rows, and whose predicate no live row satisfies, is enabled. -/
theorem enabled_of_alive {s : Store α} (wf : WF s) (br : Branch α) (nodup : br.takes.Nodup)
    (apart : ∀ id ∈ br.reads, id ∉ br.takes) (takes : ∀ id ∈ br.takes, Alive s id)
    (reads : ∀ id ∈ br.reads, Alive s id) (absent : AbsentHolds s br.absent) :
    (firing s br).Enabled (live s) := by
  refine ⟨vals_le_live wf br.takes nodup takes, fun a mem => ?_, fun a mem => ?_⟩
  · obtain ⟨id, idMem, val⟩ := List.mem_filterMap.mp (Multiset.mem_coe.mp mem)
    have le := vals_le_live wf (id :: br.takes) (List.nodup_cons.mpr ⟨apart id idMem, nodup⟩)
      (fun j hj => by
        rcases List.mem_cons.mp hj with rfl | hj
        · exact reads j idMem
        · exact takes j hj)
    rw [List.filterMap_cons_some val] at le
    have count := Multiset.le_iff_count.mp le a
    rw [← Multiset.cons_coe, Multiset.count_cons_self] at count
    rw [Firing.mem_sub_iff]
    exact count
  · obtain ⟨id, r, found, dead, rfl⟩ := (mem_live wf a).mp mem
    exact absent id r found dead

/-- **Validation by stamps is sound.**  A branch proposed against one store,
whose takes and reads have no death stamp now and above whose ceiling no live
row satisfies its predicate, is a firing of the store as it is now. -/
theorem validate_sound {s0 s1 : Store α} (wf0 : WF s0) (wf1 : WF s1) (later : Later s0 s1)
    (br : Branch α) (nodup : br.takes.Nodup) (apart : ∀ id ∈ br.reads, id ∉ br.takes)
    (ceiling : br.ceiling = s0.next) (held : AbsentHolds s0 br.absent)
    (takes : ∀ id ∈ br.takes, Alive s1 id) (reads : ∀ id ∈ br.reads, Alive s1 id)
    (fresh : NoNewMatch s1 br) : (firing s1 br).Enabled (live s1) :=
  enabled_of_alive wf1 br nodup apart takes reads
    ((absent_now_iff wf0 later br ceiling held).mpr fresh)

/-- The branch without its reads. -/
def Branch.dropReads (br : Branch α) : Branch α := { br with reads := [] }

/-- **Validation without rechecking reads.**  The takes, the `absent`
conditions and the outputs are a firing of the store now; nothing is claimed of
the reads at this moment. -/
theorem validate_sound_query {s0 s1 : Store α} (wf0 : WF s0) (wf1 : WF s1)
    (later : Later s0 s1) (br : Branch α) (nodup : br.takes.Nodup)
    (ceiling : br.ceiling = s0.next) (held : AbsentHolds s0 br.absent)
    (takes : ∀ id ∈ br.takes, Alive s1 id) (fresh : NoNewMatch s1 br) :
    (firing s1 br.dropReads).Enabled (live s1) :=
  validate_sound wf0 wf1 later br.dropReads nodup (fun _ h => by cases h) ceiling held takes
    (fun _ h => by cases h) fresh

namespace Controls

/-- Two copies of the atom `5`. -/
def twoCopies : Store Nat := run [.add 5, .add 5] empty

/-- A branch that takes the first copy. -/
def takeFirst : Branch Nat := ⟨[], [0], fun _ => False, 0, 2⟩

theorem wf_twoCopies : WF twoCopies := (run_later wf_empty _).1

/-- Positive: after an unrelated addition the branch validates by stamps and
is a firing of the later store. -/
theorem validates_after_unrelated_add :
    (firing (run [.add 7] twoCopies) takeFirst).Enabled (live (run [.add 7] twoCopies)) := by
  have step := run_later wf_twoCopies [Write.add 7]
  refine validate_sound wf_twoCopies step.1 step.2 takeFirst (by decide) (fun _ h => by cases h)
    rfl (fun _ _ _ _ h => h) (fun id mem => ?_) (fun _ h => by cases h) (fun _ _ _ _ _ h => h)
  have : id = 0 := by simpa [takeFirst] using mem
  subst this
  exact ⟨⟨5, 1, none⟩, rfl, rfl⟩

/-- Negative: once the first copy is removed, the stamp test refuses the
branch, though a copy of the atom is stored and the count rule accepts. -/
theorem stamps_refuse_where_counts_accept :
    ¬ Alive (run [.remove 0] twoCopies) 0 ∧
      (firing (run [.remove 0] twoCopies) takeFirst).takes ≤ live (run [.remove 0] twoCopies) := by
  constructor
  · rintro ⟨r, found, dead⟩
    have : r = ⟨5, 1, some 3⟩ := by
      have h : (run [Write.remove 0] twoCopies).row 0 = some ⟨5, 1, some 3⟩ := by decide
      rw [h] at found
      exact (Option.some.inj found).symm
    subst this
    cases dead
  · decide

/-- A branch with no rows that requires `7` absent, proposed on the empty
store. -/
def unlessSeven : Branch Nat := ⟨[], [], fun a => a = 7, 0, 0⟩

/-- Negative: after `7` is added, every row of the branch's footprint is as it
was (it has none), and the branch is not a firing: only the test above the
ceiling sees the added row. -/
theorem row_stamps_miss_an_added_row :
    (∀ id ∈ unlessSeven.takes ++ unlessSeven.reads, Alive (run [.add 7] (empty : Store Nat)) id) ∧
      ¬ NoNewMatch (run [.add 7] (empty : Store Nat)) unlessSeven ∧
      ¬ (firing (run [.add 7] (empty : Store Nat)) unlessSeven).Enabled
        (live (run [.add 7] (empty : Store Nat))) := by
  refine ⟨fun _ h => (by cases h), fun fresh => ?_, fun en => ?_⟩
  · exact fresh 0 ⟨7, 1, none⟩ (Nat.zero_le _) rfl rfl rfl
  · exact en.2.2 7 (by decide) rfl

/-- One row holding `5`. -/
def oneRow : Store Nat := run [.add 5] empty

/-- A branch that only reads that row. -/
def readOnly : Branch Nat := ⟨[0], [], fun _ => False, 0, 1⟩

/-- **Two laws that cannot both be kept.**  After the row is removed, it is
still an answer of the view the reader entered with (visible at time `1`), and
the reads-only branch is not a firing of the store now.  Delivering every
answer of the entry view delivers a branch that is no current firing;
delivering only current firings drops an answer of the entry view. -/
theorem snapshot_reads_or_current_firing :
    atTime (run [.remove 0] oneRow) 1 0 = some (0, 5) ∧
      ¬ (firing (run [.remove 0] oneRow) readOnly).Enabled (live (run [.remove 0] oneRow)) ∧
      (firing (run [.remove 0] oneRow) readOnly.dropReads).Enabled
        (live (run [.remove 0] oneRow)) := by
  refine ⟨by decide, fun en => ?_, ?_⟩
  · have := en.2.1 5 (by decide)
    revert this
    decide
  · have step := run_later (run_later wf_empty [Write.add 5]).1 [Write.remove 0]
    exact validate_sound_query (run_later wf_empty [Write.add 5]).1 step.1 step.2 readOnly
      (by decide) rfl (fun _ _ _ _ h => h) (fun _ h => by cases h) (fun _ _ _ _ _ h => h)

end Controls

end Mettapedia.Machines.Step.StampValidation
