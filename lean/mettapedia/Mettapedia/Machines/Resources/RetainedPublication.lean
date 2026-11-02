import Mettapedia.Machines.Resources.StateIndexed

/-!
# A bounded two-bank publication instance

The inactive bank may be reused only when it has no retained readers. Each
retention has a fresh identity and release consumes that identity. Copying the
handle's representation cannot release another reader's hold. Publication
advances the revision without wrapping. This is a concrete retention adapter,
not the storage policy required of serial Linen tables.

An immutable observation is recorded in ghost history; dereferencing its former
bank also requires a live retention handle. This history is specification state,
not a requirement to allocate an unbounded runtime log.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Resources.RetainedPublication

variable {V : Type}

structure State (V : Type) where
  banks : Bool → Option (Cell V)
  readers : Bool → Finset Nat
  nextKeep : Nat
  head : Bool
  revision : Nat
  history : List (Cell V)

structure View (V : Type) where
  bank : Bool
  keep : Nat
  captured : Cell V

def Valid (s : State V) : Prop :=
  Disjoint (s.readers false) (s.readers true) ∧
  ∀ bank id, id ∈ s.readers bank → 0 < id ∧ id ≤ s.nextKeep

def Readable (s : State V) (view : View V) : Prop :=
  view.keep ∈ s.readers view.bank ∧ s.banks view.bank = some view.captured

def Observed (s : State V) (cell : Cell V) : Prop := cell ∈ s.history

def retain (maximum : Nat) (s : State V) : Option (State V × View V) :=
  if s.nextKeep < maximum then
    match s.banks s.head with
    | none => none
    | some cell => some ({ s with readers := Function.update s.readers s.head (insert (s.nextKeep+1) (s.readers s.head)), nextKeep := s.nextKeep+1 }, ⟨s.head, s.nextKeep+1, cell⟩)
  else none

def publish (maximum : Nat) (s : State V) (value : V) : Option (State V) :=
  if s.readers (!s.head) = ∅ ∧ s.revision < maximum then
    let cell := Cell.mk ⟨s.revision + 1⟩ value
    some { s with banks := Function.update s.banks (!s.head) (some cell), head := (!s.head), revision := s.revision + 1, history := cell :: s.history }
  else none

theorem retain_readable {s next : State V} {view : View V} (maximum : Nat)
    (accepted : retain maximum s = some (next, view)) : Readable next view := by
  unfold retain at accepted
  split at accepted
  · cases found : s.banks s.head with
    | none => simp [found] at accepted
    | some cell =>
      simp [found] at accepted
      obtain ⟨rfl, rfl⟩ := accepted
      simp [Readable, found]
  · cases accepted

theorem publication_preserves_retained_view {s next : State V} {view : View V}
    (maximum : Nat) (value : V) (held : Readable s view)
    (accepted : publish maximum s value = some next) : Readable next view := by
  unfold publish at accepted
  split at accepted
  · rename_i room
    have different : view.bank ≠ !s.head := by
      intro same
      have member := held.1
      rw [same, room.1] at member
      exact Finset.notMem_empty _ member
    cases Option.some.inj accepted
    simpa [Readable, different] using held
  · cases accepted

theorem publication_preserves_observation {s next : State V} {cell : Cell V}
    (maximum : Nat) (value : V) (old : Observed s cell)
    (accepted : publish maximum s value = some next) : Observed next cell := by
  unfold publish at accepted
  split at accepted
  · cases Option.some.inj accepted
    exact List.mem_cons_of_mem _ old
  · cases accepted

theorem publication_advances_revision {s next : State V} (maximum : Nat) (value : V)
    (accepted : publish maximum s value = some next) :
    next.revision = s.revision + 1 ∧ next.revision ≤ maximum := by
  unfold publish at accepted
  split at accepted
  · cases Option.some.inj accepted
    constructor
    · rfl
    · dsimp; omega
  · cases accepted

theorem retained_inactive_blocks (maximum : Nat) (s : State V) (value : V)
    (held : (s.readers (!s.head)).Nonempty) : publish maximum s value = none := by
  simp [publish, Finset.nonempty_iff_ne_empty.mp held]

def release (s : State V) (view : View V) : Option (State V) :=
  if view.keep ∈ s.readers view.bank then
    some { s with readers := Function.update s.readers view.bank ((s.readers view.bank).erase view.keep) }
  else none

theorem release_consumes_only_its_keep {s next : State V} (released held : View V)
    (different : held.keep ≠ released.keep) (readable : Readable s held)
    (accepted : release s released = some next) : Readable next held := by
  unfold release at accepted
  split at accepted
  · cases Option.some.inj accepted
    by_cases same : held.bank = released.bank
    · simpa [Readable, same, different] using readable
    · simpa [Readable, same] using readable
  · cases accepted

theorem duplicate_release_refused {s next : State V} (view : View V)
    (accepted : release s view = some next) : release next view = none := by
  unfold release at accepted
  split at accepted
  · cases Option.some.inj accepted
    simp [release]
  · cases accepted

theorem fresh_keep_not_previously_held (s : State V) (valid : Valid s) (bank : Bool) :
    s.nextKeep + 1 ∉ s.readers bank := by
  intro member
  have bounded := (valid.2 bank _ member).2
  omega

theorem retain_preserves_valid {s next : State V} {view : View V} (valid : Valid s)
    (maximum : Nat) (accepted : retain maximum s = some (next, view)) : Valid next := by
  unfold retain at accepted
  split at accepted
  · cases found : s.banks s.head with
    | none => simp [found] at accepted
    | some cell =>
      simp [found] at accepted
      obtain ⟨rfl, rfl⟩ := accepted
      constructor
      · apply Finset.disjoint_left.mpr
        intro id left right
        cases head : s.head with
        | false =>
          simp only [head, Function.update_self, Function.update_of_ne (by decide : true ≠ false)] at left right
          rcases Finset.mem_insert.mp left with fresh | old
          · exact fresh_keep_not_previously_held s valid true (fresh ▸ right)
          · exact Finset.disjoint_left.mp valid.1 old right
        | true =>
          simp only [head, Function.update_self, Function.update_of_ne (by decide : false ≠ true)] at left right
          rcases Finset.mem_insert.mp right with fresh | old
          · exact fresh_keep_not_previously_held s valid false (fresh ▸ left)
          · exact Finset.disjoint_left.mp valid.1 left old
      · intro bank id member
        by_cases same : bank = s.head
        · subst bank
          simp only [Function.update_self] at member
          rcases Finset.mem_insert.mp member with fresh | old
          · subst id; exact ⟨Nat.zero_lt_succ _, le_rfl⟩
          · have bounds := valid.2 s.head id old; exact ⟨bounds.1, by dsimp; omega⟩
        · simp only [Function.update_of_ne same] at member
          have bounds := valid.2 bank id member
          exact ⟨bounds.1, by dsimp; omega⟩
  · cases accepted

theorem publish_preserves_valid {s next : State V} (valid : Valid s)
    (maximum : Nat) (value : V) (accepted : publish maximum s value = some next) : Valid next := by
  unfold publish at accepted
  split at accepted
  · cases Option.some.inj accepted; exact valid
  · cases accepted

theorem release_preserves_valid {s next : State V} (valid : Valid s) (view : View V)
    (accepted : release s view = some next) : Valid next := by
  unfold release at accepted
  split at accepted
  · cases Option.some.inj accepted
    have subset : ∀ bank, Function.update s.readers view.bank ((s.readers view.bank).erase view.keep) bank ⊆ s.readers bank := by
      intro bank
      by_cases same : bank = view.bank
      · subst bank; simpa using Finset.erase_subset view.keep (s.readers view.bank)
      · simp [same]
    constructor
    · exact Finset.disjoint_left.mpr fun id left right =>
        Finset.disjoint_left.mp valid.1 (subset false left) (subset true right)
    · intro bank id member; exact valid.2 bank id (subset bank member)
  · cases accepted

def start : State Nat := ⟨fun bank => if bank then none else some ⟨⟨1⟩, 10⟩,
  fun _ => ∅, 0, false, 1, [⟨⟨1⟩, 10⟩]⟩

def first : State Nat := (publish 10 start 20).getD start
def oldHeld : State Nat := { first with readers := fun bank => if bank then ∅ else {1}, nextKeep := 1 }

theorem old_bank_survives_first_publication : first.banks false = some ⟨⟨1⟩, 10⟩ := by decide
theorem both_banks_busy : publish 10 oldHeld 30 = none := by decide
theorem release_permits_next_publication :
    ((release oldHeld ⟨false, 1, ⟨⟨1⟩, 10⟩⟩).bind fun s => publish 10 s 30).isSome = true := by decide
theorem distinct_reader_survives_copied_handle_release :
    let shared := { oldHeld with readers := fun bank => if bank then ∅ else {1, 2}, nextKeep := 2 }
    let after := (release shared ⟨false, 1, ⟨⟨1⟩, 10⟩⟩).getD shared
    release after ⟨false, 1, ⟨⟨1⟩, 10⟩⟩ = none ∧ Readable after ⟨false, 2, ⟨⟨1⟩, 10⟩⟩ := by
  simp [release, Readable, oldHeld, first, publish, start]

theorem exhausted_revision_refused : publish 1 start 20 = none := by decide
theorem replaced_unretained_view_is_not_readable :
    ¬ Readable ((publish 10 first 30).getD first) ⟨false, 1, ⟨⟨1⟩, 10⟩⟩ := by
  simp [Readable, publish, first, start]

#print axioms publication_preserves_retained_view
#print axioms publication_preserves_observation
#print axioms release_consumes_only_its_keep
#print axioms duplicate_release_refused

end Mettapedia.Machines.Resources.RetainedPublication
