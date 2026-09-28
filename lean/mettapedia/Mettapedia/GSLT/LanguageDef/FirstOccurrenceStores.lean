import Mathlib.Data.Finset.Lattice.Lemmas
import Mathlib.Data.Finset.SDiff
import Mettapedia.GSLT.LanguageDef.AuthoritativeSlotTrailCompilation

/-!
# First-occurrence stores and the store trail

The compiled open equation tier runs an equation body as a tree of paths over
the activation's slot vector.  A choice point records a restore state, and a
restore resumes the path at the choice point.  The tier writes a slot in place,
with no entry on the undo trail, when its first occurrence on every path is a
store that writes a complete value into it and reads nothing from it; the
activation leaves such a slot unassigned.  Such a write goes on a separate
store trail exactly when a choice point newer than the activation is live, and
restoring the choice point empties the slot again.  This module proves that
discipline observationally equal to trailing every write, proves that it never
leaves a stale slot, and shows that without the store trail a stale slot
survives a restore.

**Model.**  A `Body` is a tree whose nodes are `Step`s: the slots a step reads,
the slots it writes, whether it is a choice point, and an effect that depends
only on the read slots and an input (a call's answer, a match row, a host
answer) and gives the written values and the branch taken.  A position is the
list of branch outcomes from the root (`Body.follow`).  `Body.defined U pos` is
the set of slots of `U` written strictly above `pos`.  `Body.FirstStores U`
says that at every position the slots of `U` the step reads are in `defined`
and the slots of `U` it writes are not; `Body.StoresFresh U` is its write half.
`Body.firstStores?` and `Body.storesFresh?` check them.

A machine configuration holds a position, the slots with their value-restoring
undo trail (`AuthoritativeSlotTrailCompilation`), the store trail, and the live
frames; a frame records its position and both trails' lengths.  A
`Discipline` names the slots written in place and whether in-place writes made
while a frame is live go on the store trail: `Discipline.trailed` writes
nothing in place, `Discipline.untrailed U` writes `U` in place and never undoes
it, `Discipline.storeTrailed U` is the tier's.  A step event carries an input
and whether a choice step leaves alternatives; only then does it push a frame,
before its writes.  A backtrack pops the newest frame, rolls the undo trail
back to its mark, empties the slots the store trail names from its store mark
on, and returns to its position, where the step runs again on the next input.
Observations (`Obs`) are the visited position with the values of the slots the
step reads and writes, or the position a backtrack returns to.

**Results for the tier's discipline.**

* `exec_observations_eq` (keystone): when the activation leaves the slots of
  `U` unassigned and the body meets `StoresFresh U`, the store-trailed and the
  trailed discipline accept the same event lists from the entry and show the
  same observations.  `exec_mirrors` is the lock-step simulation behind it
  (`Mirror`); `exec_slots_eq` adds that the two slot vectors are equal.
* `storeTrailed_unstored`: in every configuration the store-trailed
  discipline reaches, a slot of `U` the current path has not stored is empty.
* `storeTrailed_collector_safe`: every non-empty slot of `U` holds the value
  written by the most recent visit of its store, on the current path above the
  point where the activation resumes; `storeTrailed_nonempty_restricted`: a
  collector tracing every non-empty slot stays within the bound of
  `restricted_reader_agrees`.
* `inPlace_most_recent_store`: under either discipline that writes `U` in
  place, a slot of `U` the path has stored holds the value of its most recent
  store (`Trailed` is the frame and store-trail invariant behind it);
  `read_sees_most_recent_store` states for every discipline that each read of
  a slot of `U` sees the value of the most recent visit of its store.
* `Body.firstStoreSlots_firstStores`: the compile-time classification
  (`Body.classify`), which walks every path, marks a slot celled where its
  first mention reads it and stored where its first mention writes it, and
  keeps the stored slots never celled, yields slots meeting `FirstStores`.

**Results for the discipline without the store trail.**
`exec_observations_eq_untrailed`: under `FirstStores U` it is observationally
equal to the trailed one (`exec_corresponds`, `Stack`).
`restricted_reader_agrees`: a reader of the slot vector that inspects only
slots outside `U` and slots stored on the current path cannot tell the two
apart.  A reader of the whole vector can.

**Witnesses.**  `Canary.untrailed_keeps_stale_slot`: the untrailed discipline
reaches a configuration whose slot of `U` holds a value the current path never
stored; `Canary.storedAfterCall_disciplines`: at that point the trailed and the
store-trailed discipline hold nothing there, and all three show the same
observations.  `Canary.readBeforeStore_counterTrace` and
`Canary.readBeforeStore_observable`: when one branch reads a slot the other
stores, the untrailed in-place write becomes observable, while the store trail
restores equality (`Canary.readBeforeStore_storeTrailed_equal`); the
classification refuses that slot (`Canary.classification_witnesses`).

**Correspondence with the C tier.**  A test branches to its two successors; a
return, a failure or a tail call ends a path.  A call, a match and a host step
are choice points whose frames resume the same activation after the step: the
model's backtrack runs the choice step again on the next alternative, the
callee's next answer, the next row or the host's next answer.  A frame pushed
inside a callee resumes the caller only through the call's continuation, so
for the caller's slots it is a backtrack into the call step, and the frames of
the model are the frames newer than the activation.  The last alternative of a
frame is taken after popping it, which is a step event whose `more` is false.
At activation every slot head matching leaves unset receives a fresh cell,
except the slots the classification marks, which stay null, and the slot
vector's header records how many frames are live.  A primitive, a binding, or
a host step the region decides, whose pattern is such a slot at its first
occurrence, stores its result there; it appends the slot to the store trail
exactly when more frames are live than the header records, which is
`recorded` with the model's frames.  A host step the host must answer stores a
fresh cell there before pushing its frame, and the host's answers bind the
cell; the model instead writes each answer's resolved value after the frame,
which it trails.  A restore resets the region's allocation, unwinds the cell
trail, pops the store trail down to the frame's store mark emptying each slot
it names, and discards younger cells.  In the discipline without the
optimization each such slot holds a fresh cell that the store binds, trailed
whenever a frame is newer than the cell; the model represents that binding as a
trailed write of the slot, undone by a restore.  Slot values in the model are
the slots' resolved meanings.  The classification pass seeds the mentioned
slots with those the activation assigns (head variables, the output slot) or
reads (the destination and output templates), marks them celled, and treats a
store-able step whose slot is already mentioned as a unification, which reads
the slot: that is `Body.classify` under `Body.WritesFirst`.

**The collector.**  Besides the steps' templates, the region collector reads
slot vectors: it traces and copies every non-null slot of every vector a live
continuation reaches, and it carries the store trail along, dropping the
entries of vectors no continuation reaches.  `storeTrailed_collector_safe` is
the property it relies on: with the store trail no non-null slot of `U` holds a
value the current path did not store.

**Not covered.**  The region's cells and the unifier, which the inputs
abstract: the disciplines perform the same cell operations, except the
per-slot cells of the unoptimized discipline, whose bindings are the modelled
slot writes, so cell indices differ between runs and answers agree up to the
names of unbound variables.  The collector's copying and its renaming of the
store trail and of store marks are not modelled.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.FirstOccurrenceStores

open FiniteEnvironmentCompilation
open AuthoritativeSlotTrailCompilation

universe uKey uValue uInput

/-! ## Bodies: trees of paths -/

section Program

variable {Key : Type uKey} (inventory : Inventory Key) (Value : Type uValue)
  (Input : Type uInput)

/-- One step of a body over the activation's slots: the slots it reads, the
slots it writes, whether it is a choice point, and its effect.  The effect sees
the slots and an input (the answer of a call, a row of a match, a host answer),
and either fails or gives the values of the written slots and the branch taken.
It depends only on the slots the step reads. -/
structure Step where
  reads : Finset inventory.Slot
  writes : List inventory.Slot
  choice : Bool
  run : DenseEnvironment inventory Value → Input →
    Option ((inventory.Slot → Value) × Bool)
  run_congr : ∀ slots slots' input, (∀ i ∈ reads, slots i = slots' i) →
    run slots input = run slots' input

/-- A body: steps in sequence, each continuing at the successor its branch
outcome selects.  Paths end at `stop` and never rejoin.  A step that does not
branch has the same successor for both outcomes. -/
inductive Body where
  | stop
  | node (step : Step inventory Value Input) (next : Bool → Body)

end Program

/-- The slots a step mentions: those it reads and those it writes. -/
def Step.mentions {Key : Type uKey} {inventory : Inventory Key} {Value : Type uValue}
    {Input : Type uInput} (step : Step inventory Value Input) : Finset inventory.Slot :=
  step.reads ∪ step.writes.toFinset

namespace Body

variable {Key : Type uKey} {inventory : Inventory Key} {Value : Type uValue}
  {Input : Type uInput}

/-- The subtree at a position, a position being the branch outcomes of the
steps on the path from the root. -/
def follow : Body inventory Value Input → List Bool → Body inventory Value Input
  | body, [] => body
  | .stop, _ :: _ => .stop
  | .node _ next, outcome :: rest => (next outcome).follow rest

@[simp] theorem follow_nil (body : Body inventory Value Input) :
    body.follow [] = body := by
  cases body <;> rfl

@[simp] theorem stop_follow (pos : List Bool) :
    (Body.stop : Body inventory Value Input).follow pos = .stop := by
  cases pos <;> rfl

/-- The step at `pos` writes the slot `i`. -/
def WritesAt (body : Body inventory Value Input) (pos : List Bool)
    (i : inventory.Slot) : Prop :=
  ∃ step next, body.follow pos = .node step next ∧ i ∈ step.writes

/-- The slots of `U` written on the path strictly before `pos`. -/
def defined (U : Finset inventory.Slot) :
    Body inventory Value Input → List Bool → Finset inventory.Slot
  | _, [] => ∅
  | .stop, _ :: _ => ∅
  | .node step next, outcome :: rest =>
      step.writes.toFinset ∩ U ∪ (next outcome).defined U rest

theorem mem_defined_iff (U : Finset inventory.Slot) {i : inventory.Slot} :
    ∀ (body : Body inventory Value Input) (pos : List Bool),
      i ∈ body.defined U pos ↔
        i ∈ U ∧ ∃ above outcome, above ++ [outcome] <+: pos ∧ body.WritesAt above i
  | _, [] => by simp [defined]
  | .stop, _ :: _ => by simp [defined, WritesAt]
  | .node step next, outcome :: rest => by
      rw [defined, Finset.mem_union, Finset.mem_inter, List.mem_toFinset,
        mem_defined_iff U (next outcome) rest]
      constructor
      · rintro (⟨written, direct⟩ | ⟨direct, above, last, prefixed, writes⟩)
        · exact ⟨direct, [], outcome, by simp, step, next, rfl, written⟩
        · exact ⟨direct, outcome :: above, last, by simpa using prefixed, writes⟩
      · rintro ⟨direct, above, last, prefixed, writes⟩
        cases above with
        | nil =>
            obtain ⟨step', next', found, written⟩ := writes
            cases found
            exact .inl ⟨written, direct⟩
        | cons first above =>
            rw [List.cons_append, List.cons_prefix_cons] at prefixed
            obtain ⟨rfl, prefixed⟩ := prefixed
            exact .inr ⟨direct, above, last, prefixed, writes⟩

theorem defined_mono (U : Finset inventory.Slot) (body : Body inventory Value Input)
    {pos pos' : List Bool} (prefixed : pos <+: pos') :
    body.defined U pos ⊆ body.defined U pos' := by
  intro i member
  rw [mem_defined_iff] at member ⊢
  obtain ⟨direct, above, outcome, below, writes⟩ := member
  exact ⟨direct, above, outcome, below.trans prefixed, writes⟩

theorem defined_append (U : Finset inventory.Slot) (body : Body inventory Value Input)
    {pos : List Bool} {step : Step inventory Value Input}
    {next : Bool → Body inventory Value Input}
    (found : body.follow pos = .node step next) (outcome : Bool) :
    body.defined U (pos ++ [outcome]) =
      body.defined U pos ∪ step.writes.toFinset ∩ U := by
  induction pos generalizing body with
  | nil =>
      rw [follow_nil] at found
      subst found
      simp [defined]
  | cons first pos inductionHypothesis =>
      cases body with
      | stop => simp [follow] at found
      | node step' next' =>
          rw [List.cons_append, defined, defined,
            inductionHypothesis (next' first) found, Finset.union_assoc]

/-- **The first-occurrence condition** for the slots `U`: at every position,
the slots of `U` the step reads are written earlier on the path, and the slots
of `U` it writes are not.  So on every path the first occurrence of a slot of
`U` writes it without reading it, and no later step of the path writes it. -/
def FirstStores (U : Finset inventory.Slot) (body : Body inventory Value Input) :
    Prop :=
  ∀ pos step next, body.follow pos = .node step next →
    step.reads ∩ U ⊆ body.defined U pos ∧
      ∀ i ∈ step.writes, i ∈ U → i ∉ body.defined U pos

/-- The compile-time check of the condition, walking every path with the slots
of `U` already stored on it. -/
def firstStores? (U : Finset inventory.Slot) :
    Finset inventory.Slot → Body inventory Value Input → Bool
  | _, .stop => true
  | stored, .node step next =>
      decide (step.reads ∩ U ⊆ stored) &&
        step.writes.all (fun i => !(decide (i ∈ U) && decide (i ∈ stored))) &&
        firstStores? U (stored ∪ step.writes.toFinset ∩ U) (next true) &&
        firstStores? U (stored ∪ step.writes.toFinset ∩ U) (next false)

theorem firstStores?_sound_from (U : Finset inventory.Slot) :
    ∀ (stored : Finset inventory.Slot) (body : Body inventory Value Input),
      firstStores? U stored body = true →
      ∀ pos step next, body.follow pos = .node step next →
        step.reads ∩ U ⊆ stored ∪ body.defined U pos ∧
          ∀ i ∈ step.writes, i ∈ U → i ∉ stored ∪ body.defined U pos
  | stored, .stop, _, pos, step, next, found => by simp at found
  | stored, .node step' next', accepted, [], step, next, found => by
      cases found
      simp only [firstStores?, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
        Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not] at accepted
      obtain ⟨⟨⟨readsStored, writesFresh⟩, _⟩, _⟩ := accepted
      refine ⟨by simpa [defined] using readsStored, fun i member direct => ?_⟩
      rcases writesFresh i member with notDirect | notStored
      · exact (notDirect direct).elim
      · simpa [defined] using notStored
  | stored, .node step' next', accepted, outcome :: rest, step, next, found => by
      simp only [firstStores?, Bool.and_eq_true] at accepted
      obtain ⟨⟨_, acceptedTrue⟩, acceptedFalse⟩ := accepted
      have acceptedNext : firstStores? U (stored ∪ step'.writes.toFinset ∩ U)
          (next' outcome) = true := by
        cases outcome
        · exact acceptedFalse
        · exact acceptedTrue
      have inner := firstStores?_sound_from U _ (next' outcome) acceptedNext rest step
        next found
      simpa [defined, Finset.union_assoc] using inner

/-- The check establishes the first-occurrence condition. -/
theorem firstStores?_sound (U : Finset inventory.Slot) (body : Body inventory Value Input)
    (accepted : firstStores? U ∅ body = true) : body.FirstStores U := by
  intro pos step next found
  simpa using firstStores?_sound_from U ∅ body accepted pos step next found

/-- The compile-time check of the write half, walking every path with the
slots of `U` already stored on it. -/
def storesFresh? (U : Finset inventory.Slot) :
    Finset inventory.Slot → Body inventory Value Input → Bool
  | _, .stop => true
  | stored, .node step next =>
      step.writes.all (fun i => !(decide (i ∈ U) && decide (i ∈ stored))) &&
        storesFresh? U (stored ∪ step.writes.toFinset ∩ U) (next true) &&
        storesFresh? U (stored ∪ step.writes.toFinset ∩ U) (next false)

theorem storesFresh?_sound_from (U : Finset inventory.Slot) :
    ∀ (stored : Finset inventory.Slot) (body : Body inventory Value Input),
      storesFresh? U stored body = true →
      ∀ pos step next, body.follow pos = .node step next →
        ∀ i ∈ step.writes, i ∈ U → i ∉ stored ∪ body.defined U pos
  | stored, .stop, _, pos, step, next, found => by simp at found
  | stored, .node step' next', accepted, [], step, next, found => by
      cases found
      simp only [storesFresh?, Bool.and_eq_true, List.all_eq_true,
        Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not] at accepted
      obtain ⟨⟨writesFresh, _⟩, _⟩ := accepted
      intro i member direct
      rcases writesFresh i member with notDirect | notStored
      · exact (notDirect direct).elim
      · simpa [defined] using notStored
  | stored, .node step' next', accepted, outcome :: rest, step, next, found => by
      simp only [storesFresh?, Bool.and_eq_true] at accepted
      obtain ⟨⟨_, acceptedTrue⟩, acceptedFalse⟩ := accepted
      have acceptedNext : storesFresh? U (stored ∪ step'.writes.toFinset ∩ U)
          (next' outcome) = true := by
        cases outcome
        · exact acceptedFalse
        · exact acceptedTrue
      intro i member direct
      have inner := storesFresh?_sound_from U _ (next' outcome) acceptedNext rest step
        next found i member direct
      simpa [defined, Finset.union_assoc] using inner

/-- The write half of the first-occurrence condition: a slot of `U` is written
only where the path has not stored it. -/
def StoresFresh (U : Finset inventory.Slot) (body : Body inventory Value Input) :
    Prop :=
  ∀ pos step next, body.follow pos = .node step next →
    ∀ i ∈ step.writes, i ∈ U → i ∉ body.defined U pos

theorem FirstStores.storesFresh {U : Finset inventory.Slot}
    {body : Body inventory Value Input} (firstStores : body.FirstStores U) :
    body.StoresFresh U :=
  fun pos step next found => (firstStores pos step next found).2

/-- The check establishes the write half. -/
theorem storesFresh?_sound (U : Finset inventory.Slot) (body : Body inventory Value Input)
    (accepted : storesFresh? U ∅ body = true) : body.StoresFresh U := by
  intro pos step next found i written direct
  simpa using storesFresh?_sound_from U ∅ body accepted pos step next found i written direct

/-- On every path, a slot of `U` is written at one position only. -/
theorem StoresFresh.writesAt_unique {U : Finset inventory.Slot}
    {body : Body inventory Value Input} (storesFresh : body.StoresFresh U)
    {i : inventory.Slot} (direct : i ∈ U) {pos first second : List Bool}
    {firstOutcome secondOutcome : Bool}
    (firstBelow : first ++ [firstOutcome] <+: pos)
    (secondBelow : second ++ [secondOutcome] <+: pos)
    (firstWrites : body.WritesAt first i) (secondWrites : body.WritesAt second i) :
    first = second := by
  have earlier : ∀ {early late : List Bool} {earlyOutcome lateOutcome : Bool},
      early ++ [earlyOutcome] <+: pos → late ++ [lateOutcome] <+: pos →
      early.length < late.length → body.WritesAt early i → ¬ body.WritesAt late i := by
    intro early late earlyOutcome lateOutcome earlyBelow lateBelow shorter earlyWrites
      lateWrites
    have earlyAbove : early ++ [earlyOutcome] <+: late :=
      List.prefix_of_prefix_length_le earlyBelow
        ((List.prefix_append late [lateOutcome]).trans lateBelow)
        (by simp; omega)
    obtain ⟨step, next, found, written⟩ := lateWrites
    exact storesFresh late step next found i written direct
      ((mem_defined_iff U body late).mpr ⟨direct, early, earlyOutcome, earlyAbove,
        earlyWrites⟩)
  rcases Nat.lt_trichotomy first.length second.length with shorter | same | longer
  · exact (earlier firstBelow secondBelow shorter firstWrites secondWrites).elim
  · exact List.IsPrefix.eq_of_length
      (List.prefix_of_prefix_length_le
        ((List.prefix_append first [firstOutcome]).trans firstBelow)
        ((List.prefix_append second [secondOutcome]).trans secondBelow)
        (le_of_eq same)) same
  · exact (earlier secondBelow firstBelow longer secondWrites firstWrites).elim

/-! ### The classification pass -/

/-- The slots mentioned on the path strictly before `pos`. -/
def seen : Body inventory Value Input → List Bool → Finset inventory.Slot
  | _, [] => ∅
  | .stop, _ :: _ => ∅
  | .node step next, outcome :: rest => step.mentions ∪ (next outcome).seen rest

theorem mem_seen_iff {i : inventory.Slot} :
    ∀ (body : Body inventory Value Input) (pos : List Bool),
      i ∈ body.seen pos ↔
        ∃ above outcome, above ++ [outcome] <+: pos ∧
          ∃ step next, body.follow above = .node step next ∧ i ∈ step.mentions
  | _, [] => by simp [seen]
  | .stop, _ :: _ => by simp [seen]
  | .node step next, outcome :: rest => by
      rw [seen, Finset.mem_union, mem_seen_iff (next outcome) rest]
      constructor
      · rintro (mentioned | ⟨above, last, prefixed, found⟩)
        · exact ⟨[], outcome, by simp, step, next, rfl, mentioned⟩
        · exact ⟨outcome :: above, last, by simpa using prefixed, found⟩
      · rintro ⟨above, last, prefixed, found⟩
        cases above with
        | nil =>
            obtain ⟨step', next', found, mentioned⟩ := found
            cases found
            exact .inl mentioned
        | cons first above =>
            rw [List.cons_append, List.cons_prefix_cons] at prefixed
            obtain ⟨rfl, prefixed⟩ := prefixed
            exact .inr ⟨above, last, prefixed, found⟩

theorem defined_subset_seen (U : Finset inventory.Slot) (body : Body inventory Value Input)
    (pos : List Bool) : body.defined U pos ⊆ body.seen pos := by
  intro i member
  obtain ⟨_, above, outcome, prefixed, step, next, found, written⟩ :=
    (mem_defined_iff U body pos).mp member
  exact (mem_seen_iff body pos).mpr ⟨above, outcome, prefixed, step, next, found,
    Finset.mem_union_right _ (List.mem_toFinset.mpr written)⟩

/-- A mentioned slot has a first mention on the path. -/
theorem exists_first_mention (body : Body inventory Value Input) {i : inventory.Slot} :
    ∀ (bound : Nat) (pos : List Bool), pos.length ≤ bound → i ∈ body.seen pos →
      ∃ above outcome, above ++ [outcome] <+: pos ∧
        (∃ step next, body.follow above = .node step next ∧ i ∈ step.mentions) ∧
        i ∉ body.seen above
  | 0, pos, short, member => by
      have empty : pos = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp short)
      subst empty
      simp [seen] at member
  | bound + 1, pos, short, member => by
      obtain ⟨above, outcome, prefixed, found⟩ := (mem_seen_iff body pos).mp member
      by_cases earlier : i ∈ body.seen above
      · have shorter : above.length ≤ bound := by
          have := prefixed.length_le
          simp at this
          omega
        obtain ⟨first, firstOutcome, firstPrefixed, firstFound, fresh⟩ :=
          exists_first_mention body bound above shorter earlier
        exact ⟨first, firstOutcome,
          firstPrefixed.trans ((List.prefix_append above [outcome]).trans prefixed),
          firstFound, fresh⟩
      · exact ⟨above, outcome, prefixed, found, earlier⟩

/-- The compile-time classification, walking every path with the slots the
path has mentioned: a slot is *celled* where its first mention reads it, and
*stored* where its first mention writes it without reading it.  The result is
the pair (celled, stored). -/
def classify : Finset inventory.Slot → Body inventory Value Input →
    Finset inventory.Slot × Finset inventory.Slot
  | _, .stop => (∅, ∅)
  | mentioned, .node step next =>
      ((step.reads \ mentioned) ∪ (classify (mentioned ∪ step.mentions) (next true)).1 ∪
          (classify (mentioned ∪ step.mentions) (next false)).1,
        (step.writes.toFinset \ (mentioned ∪ step.reads)) ∪
          (classify (mentioned ∪ step.mentions) (next true)).2 ∪
          (classify (mentioned ∪ step.mentions) (next false)).2)

/-- A first read anywhere makes the slot celled. -/
theorem mem_classify_celled {i : inventory.Slot} :
    ∀ (mentioned : Finset inventory.Slot) (body : Body inventory Value Input)
      (pos : List Bool) (step : Step inventory Value Input)
      (next : Bool → Body inventory Value Input),
      body.follow pos = .node step next → i ∈ step.reads →
      i ∉ mentioned ∪ body.seen pos → i ∈ (classify mentioned body).1
  | mentioned, .stop, pos, step, next, found, _, _ => by simp at found
  | mentioned, .node step' next', [], step, next, found, reads, fresh => by
      cases found
      simp only [classify, Finset.mem_union, Finset.mem_sdiff]
      exact .inl (.inl ⟨reads, fun member => fresh (by simp [member])⟩)
  | mentioned, .node step' next', outcome :: rest, step, next, found, reads, fresh => by
      have inner := mem_classify_celled (mentioned ∪ step'.mentions) (next' outcome) rest
        step next found reads (by simpa [seen, Finset.union_assoc] using fresh)
      simp only [classify, Finset.mem_union]
      cases outcome
      · exact .inr inner
      · exact .inl (.inr inner)

/-- The slots the pass writes in place: stored somewhere, celled nowhere, and
not among the slots the activation itself assigns or reads. -/
def firstStoreSlots (initial : Finset inventory.Slot) (body : Body inventory Value Input) :
    Finset inventory.Slot :=
  (classify initial body).2 \ ((classify initial body).1 ∪ initial)

/-- In the reference program a write is always its slot's first mention on the
path: a later store of the slot unifies with it, which reads it. -/
def WritesFirst (initial : Finset inventory.Slot) (body : Body inventory Value Input) :
    Prop :=
  ∀ pos step next, body.follow pos = .node step next →
    ∀ i ∈ step.writes, i ∉ initial ∪ body.seen pos ∪ step.reads

/-- **The classification is sound.**  The slots the pass marks meet the
first-occurrence condition. -/
theorem firstStoreSlots_firstStores (initial : Finset inventory.Slot)
    (body : Body inventory Value Input) (writesFirst : WritesFirst initial body) :
    body.FirstStores (firstStoreSlots initial body) := by
  intro pos step next found
  constructor
  · intro i member
    obtain ⟨reads, marked⟩ := Finset.mem_inter.mp member
    obtain ⟨_, notCelledOrInitial⟩ := Finset.mem_sdiff.mp marked
    have notCelled : i ∉ (classify initial body).1 := fun celled =>
      notCelledOrInitial (Finset.mem_union_left _ celled)
    have notInitial : i ∉ initial := fun start =>
      notCelledOrInitial (Finset.mem_union_right _ start)
    have mentionedBefore : i ∈ body.seen pos := by
      by_contra fresh
      exact notCelled (mem_classify_celled initial body pos step next found reads
        (by simp [notInitial, fresh]))
    obtain ⟨above, outcome, prefixed, ⟨stepAbove, nextAbove, foundAbove, mentioned⟩,
      firstThere⟩ := exists_first_mention body pos.length pos le_rfl mentionedBefore
    have writtenAbove : i ∈ stepAbove.writes := by
      rcases Finset.mem_union.mp mentioned with readAbove | written
      · exact (notCelled (mem_classify_celled initial body above stepAbove nextAbove
          foundAbove readAbove (by simp [notInitial, firstThere]))).elim
      · exact List.mem_toFinset.mp written
    exact (mem_defined_iff _ body pos).mpr ⟨marked, above, outcome, prefixed,
      stepAbove, nextAbove, foundAbove, writtenAbove⟩
  · intro i written _ stored
    exact writesFirst pos step next found i written
      (Finset.mem_union_left _ (Finset.mem_union_right _
        (defined_subset_seen _ body pos stored)))

end Body

/-! ## Slot writes with and without the trail -/

section Writes

variable {Key : Type uKey} [DecidableEq Key] {inventory : Inventory Key}
  {Value : Type uValue}

/-- No trail entry names a slot of `U`. -/
def Clean (U : Finset inventory.Slot) (state : State inventory Value) : Prop :=
  ∀ entry ∈ state.trail, entry.slot ∉ U

/-- Write a slot in place, leaving the trail as it is. -/
def writeInPlace (state : State inventory Value) (update : DenseWrite inventory Value) :
    State inventory Value :=
  ⟨writeDense inventory state.slots update, state.trail⟩

/-- Write one slot: in place when it belongs to `direct`, through the undo trail
otherwise. -/
def put (direct : Finset inventory.Slot) (state : State inventory Value)
    (update : DenseWrite inventory Value) : State inventory Value :=
  if update.1 ∈ direct then writeInPlace state update else write inventory state update

/-- Write a list of slots in order. -/
def putAll (direct : Finset inventory.Slot) :
    State inventory Value → List (DenseWrite inventory Value) → State inventory Value
  | state, [] => state
  | state, update :: updates => putAll direct (put direct state update) updates

/-- With nothing in place, writing is the authoritative trailed execution. -/
theorem putAll_empty (state : State inventory Value)
    (updates : List (DenseWrite inventory Value)) :
    putAll ∅ state updates = run inventory state updates := by
  induction updates generalizing state with
  | nil => rfl
  | cons update updates inductionHypothesis =>
      simp only [putAll, run, put, Finset.notMem_empty, if_false]
      exact inductionHypothesis _

@[simp] theorem put_slots (direct : Finset inventory.Slot) (state : State inventory Value)
    (update : DenseWrite inventory Value) :
    (put direct state update).slots = writeDense inventory state.slots update := by
  unfold put
  split <;> rfl

/-- Both disciplines leave the same slot contents. -/
theorem putAll_slots (direct : Finset inventory.Slot) (state : State inventory Value)
    (writes : List inventory.Slot) (values : inventory.Slot → Value)
    (i : inventory.Slot) :
    (putAll direct state (writes.map fun j => (j, values j))).slots i =
      if i ∈ writes then some (values i) else state.slots i := by
  induction writes generalizing state with
  | nil => simp [putAll]
  | cons j writes inductionHypothesis =>
      rw [List.map_cons, putAll, inductionHypothesis, put_slots]
      by_cases later : i ∈ writes
      · simp [later]
      · by_cases same : i = j
        · subst same
          simp [writeDense]
        · simp [later, same, writeDense]

theorem mark_le_putAll (direct : Finset inventory.Slot) (state : State inventory Value)
    (updates : List (DenseWrite inventory Value)) :
    mark state ≤ mark (putAll direct state updates) := by
  induction updates generalizing state with
  | nil => exact le_rfl
  | cons update updates inductionHypothesis =>
      refine le_trans ?_ (inductionHypothesis _)
      unfold put mark
      split
      · exact le_rfl
      · simp [write]

theorem Clean.putAll {U : Finset inventory.Slot} {state : State inventory Value}
    (clean : Clean U state) (updates : List (DenseWrite inventory Value)) :
    Clean U (FirstOccurrenceStores.putAll U state updates) := by
  induction updates generalizing state with
  | nil => exact clean
  | cons update updates inductionHypothesis =>
      refine inductionHypothesis ?_
      unfold put
      split
      · exact clean
      · next notDirect =>
          intro entry member
          rcases List.mem_cons.mp member with same | older
          · subst same
            exact notDirect
          · exact clean entry older

theorem mark_le_of_rollbackTo? {m : Nat} {state restored : State inventory Value}
    (restores : rollbackTo? inventory m state = some restored) : m ≤ mark state := by
  unfold rollbackTo? at restores
  split at restores
  · assumption
  · cases restores

@[simp] theorem rollbackTo?_mark (state : State inventory Value) :
    rollbackTo? inventory (mark state) state = some state := by
  simp [rollbackTo?, mark, rollbackN]

/-- A trailed write above a mark is invisible to a rollback to the mark. -/
theorem rollbackTo?_write_of_le {m : Nat} {state : State inventory Value}
    (le : m ≤ mark state) (update : DenseWrite inventory Value) :
    rollbackTo? inventory m (write inventory state update) =
      rollbackTo? inventory m state := by
  have sizes : (write inventory state update).trail.length = state.trail.length + 1 := by
    simp [write]
  unfold rollbackTo?
  unfold mark at le
  rw [sizes, if_pos (by omega), if_pos le,
    show state.trail.length + 1 - m = (state.trail.length - m) + 1 by omega]
  simp [rollbackN, undoOne?_write]

theorem rollbackTo?_putAll_empty_of_le {m : Nat} {state : State inventory Value}
    (le : m ≤ mark state) (updates : List (DenseWrite inventory Value)) :
    rollbackTo? inventory m (putAll ∅ state updates) = rollbackTo? inventory m state := by
  induction updates generalizing state with
  | nil => rfl
  | cons update updates inductionHypothesis =>
      have putIsWrite : put ∅ state update = write inventory state update := by
        simp [put]
      have le' : m ≤ mark (put ∅ state update) := le.trans (mark_le_putAll ∅ state [update])
      rw [putAll, inductionHypothesis le', putIsWrite, rollbackTo?_write_of_le le]

theorem restoreEntry_writeDense_comm {environment : DenseEnvironment inventory Value}
    {entry : UndoEntry inventory Value} {update : DenseWrite inventory Value}
    (distinct : entry.slot ≠ update.1) :
    restoreEntry inventory (writeDense inventory environment update) entry =
      writeDense inventory (restoreEntry inventory environment entry) update := by
  funext candidate
  by_cases atEntry : candidate = entry.slot
  · subst atEntry
    simp [restoreEntry, writeDense, distinct]
  · by_cases atUpdate : candidate = update.1
    · subst atUpdate
      simp [restoreEntry, writeDense, atEntry]
    · simp [restoreEntry, writeDense, atEntry, atUpdate]

/-- Undoing a clean trail commutes with an in-place write of a slot of `U`. -/
theorem rollbackN_writeInPlace {U : Finset inventory.Slot} (steps : Nat)
    {state : State inventory Value} (clean : Clean U state)
    {update : DenseWrite inventory Value} (direct : update.1 ∈ U) :
    rollbackN inventory steps (writeInPlace state update) =
      (rollbackN inventory steps state).map fun restored => writeInPlace restored update := by
  induction steps generalizing state with
  | zero => rfl
  | succ steps inductionHypothesis =>
      cases state with
      | mk slots trail =>
          cases trail with
          | nil => rfl
          | cons entry rest =>
              have distinct : entry.slot ≠ update.1 := by
                intro same
                exact clean entry List.mem_cons_self (same ▸ direct)
              have restClean : Clean U ⟨restoreEntry inventory slots entry, rest⟩ :=
                fun older member => clean older (List.mem_cons_of_mem _ member)
              have step : undoOne? inventory (writeInPlace ⟨slots, entry :: rest⟩ update) =
                  some (writeInPlace ⟨restoreEntry inventory slots entry, rest⟩ update) := by
                simp [undoOne?, writeInPlace, restoreEntry_writeDense_comm distinct]
              rw [rollbackN, step]
              show rollbackN inventory steps
                  (writeInPlace ⟨restoreEntry inventory slots entry, rest⟩ update) = _
              rw [inductionHypothesis restClean]
              rfl

theorem rollbackTo?_writeInPlace {U : Finset inventory.Slot} (m : Nat)
    {state : State inventory Value} (clean : Clean U state)
    {update : DenseWrite inventory Value} (direct : update.1 ∈ U) :
    rollbackTo? inventory m (writeInPlace state update) =
      (rollbackTo? inventory m state).map fun restored => writeInPlace restored update := by
  unfold rollbackTo?
  change (if m ≤ state.trail.length then _ else none) =
    (if m ≤ state.trail.length then _ else none).map _
  split
  · exact rollbackN_writeInPlace _ clean direct
  · rfl

/-- The updates of `U` among `updates`, in order. -/
def directPart (U : Finset inventory.Slot) (updates : List (DenseWrite inventory Value)) :
    List (DenseWrite inventory Value) :=
  updates.filter fun update => decide (update.1 ∈ U)

/-- Rolling back past writes of the direct discipline undoes the trailed writes
and keeps the in-place ones. -/
theorem rollbackTo?_putAll {U : Finset inventory.Slot} {m : Nat}
    {state : State inventory Value} (clean : Clean U state) (le : m ≤ mark state)
    (updates : List (DenseWrite inventory Value)) :
    rollbackTo? inventory m (putAll U state updates) =
      (rollbackTo? inventory m state).map fun restored =>
        putAll U restored (directPart U updates) := by
  induction updates generalizing state with
  | nil => simp [putAll, directPart]
  | cons update updates inductionHypothesis =>
      have clean' : Clean U (put U state update) := clean.putAll [update]
      have le' : m ≤ mark (put U state update) :=
        le.trans (mark_le_putAll U state [update])
      rw [putAll, inductionHypothesis clean' le']
      by_cases direct : update.1 ∈ U
      · have putInPlace : put U state update = writeInPlace state update := by
          simp [put, direct]
        rw [putInPlace, rollbackTo?_writeInPlace m clean direct, Option.map_map]
        congr 1
        funext restored
        simp [directPart, direct, putAll, put]
      · have putTrailed : put U state update = write inventory state update := by
          simp [put, direct]
        rw [putTrailed, rollbackTo?_write_of_le le]
        congr 1
        funext restored
        simp [directPart, direct]

omit [DecidableEq Key] in
theorem mem_directPart {U : Finset inventory.Slot}
    {updates : List (DenseWrite inventory Value)} {update : DenseWrite inventory Value}
    (member : update ∈ directPart U updates) : update ∈ updates ∧ update.1 ∈ U := by
  simpa [directPart] using member

/-- A rollback of a clean trail keeps the slots of `U` and the trail clean. -/
theorem rollbackN_clean {U : Finset inventory.Slot} (steps : Nat) :
    ∀ {state restored : State inventory Value}, Clean U state →
      rollbackN inventory steps state = some restored →
      Clean U restored ∧ ∀ i ∈ U, restored.slots i = state.slots i := by
  induction steps with
  | zero =>
      intro state restored clean restores
      cases restores
      exact ⟨clean, fun _ _ => rfl⟩
  | succ steps inductionHypothesis =>
      intro state restored clean restores
      cases state with
      | mk slots trail =>
          cases trail with
          | nil => simp [rollbackN, undoOne?] at restores
          | cons entry rest =>
              have restClean : Clean U ⟨restoreEntry inventory slots entry, rest⟩ :=
                fun older member => clean older (List.mem_cons_of_mem _ member)
              simp only [rollbackN, undoOne?] at restores
              obtain ⟨cleanRestored, kept⟩ := inductionHypothesis restClean restores
              refine ⟨cleanRestored, fun i direct => ?_⟩
              rw [kept i direct]
              have distinct : i ≠ entry.slot := by
                intro same
                exact clean entry List.mem_cons_self (same ▸ direct)
              simp [restoreEntry, distinct]

theorem rollbackTo?_clean {U : Finset inventory.Slot} {m : Nat}
    {state restored : State inventory Value} (clean : Clean U state)
    (restores : rollbackTo? inventory m state = some restored) :
    Clean U restored ∧ ∀ i ∈ U, restored.slots i = state.slots i := by
  unfold rollbackTo? at restores
  split at restores
  · exact rollbackN_clean _ clean restores
  · cases restores

end Writes

/-! ## The machine -/

section Machine

variable {Key : Type uKey} [DecidableEq Key] {inventory : Inventory Key}
  {Value : Type uValue} {Input : Type uInput}

/-- A choice point: the position of the step that opened it, and the lengths
of the undo trail and of the store trail before that step's writes. -/
structure Frame where
  pos : List Bool
  mark : Nat
  storeMark : Nat

variable (inventory Value) in
/-- A configuration of one activation: its position, its slots with their undo
trail, the store trail (slots written in place that a restore must empty,
oldest first), and its live choice points, newest first. -/
structure Config where
  pos : List Bool
  state : State inventory Value
  stores : List inventory.Slot
  frames : List Frame

variable (inventory Value) in
/-- What the machine shows at each event: a visited step's position, the
values of the slots it reads and of the slots it writes; or the position a
backtrack returns to. -/
inductive Obs where
  | visit (pos : List Bool) (seen : DenseEnvironment inventory Value)
      (wrote : DenseEnvironment inventory Value)
  | back (pos : List Bool)

/-- The position of a visit. -/
def Obs.visited : Obs inventory Value → Option (List Bool)
  | .visit pos _ _ => some pos
  | .back _ => none

variable (Input) in
/-- An event: run the step at the current position on an input, `more` saying
whether a choice step leaves alternatives for a later backtrack; or backtrack
to the newest choice point, which then runs its step again. -/
inductive Event where
  | step (input : Input) (more : Bool)
  | back

variable (inventory) in
/-- How a machine writes slots: the slots it writes in place, and whether an
in-place write made while a choice point is live goes on the store trail. -/
structure Discipline where
  inPlace : Finset inventory.Slot
  trailsStores : Bool

/-- Every write through the undo trail: the reference. -/
def Discipline.trailed : Discipline inventory := ⟨∅, false⟩

/-- The slots of `U` written in place and never undone. -/
def Discipline.untrailed (U : Finset inventory.Slot) : Discipline inventory :=
  ⟨U, false⟩

/-- The slots of `U` written in place, on the store trail while a choice point
is live, so that restoring the choice point empties them: the tier's
discipline. -/
def Discipline.storeTrailed (U : Finset inventory.Slot) : Discipline inventory :=
  ⟨U, true⟩

/-- Empty the named slots. -/
def empty (state : State inventory Value) (slots : List inventory.Slot) :
    State inventory Value :=
  ⟨fun i => if i ∈ slots then none else state.slots i, state.trail⟩

/-- The choice points after a step: a choice step with alternatives left opens
one, recording both trails' lengths before the step's writes. -/
def opened (step : Step inventory Value Input) (more : Bool)
    (config : Config inventory Value) : List Frame :=
  if step.choice && more then
    ⟨config.pos, mark config.state, config.stores.length⟩ :: config.frames
  else config.frames

/-- The store trail after a step's writes: its in-place writes are recorded
while a choice point is live, when the discipline trails stores. -/
def recorded (discipline : Discipline inventory) (frames : List Frame)
    (stores writes : List inventory.Slot) : List inventory.Slot :=
  if discipline.trailsStores = true ∧ frames ≠ [] then
    stores ++ writes.filter fun i => decide (i ∈ discipline.inPlace)
  else stores

/-- One event of the machine under a discipline.  A step writes the slots of
`discipline.inPlace` in place and every other slot through the undo trail; a
backtrack rolls the undo trail back to the frame's mark and empties the slots
the store trail names from the frame's store mark on. -/
def next (body : Body inventory Value Input) (discipline : Discipline inventory)
    (config : Config inventory Value) :
    Event Input → Option (Obs inventory Value × Config inventory Value)
  | .step input more =>
      match body.follow config.pos with
      | .stop => none
      | .node step _ =>
          match step.run config.state.slots input with
          | none => none
          | some (values, outcome) =>
              some (.visit config.pos
                  (fun i => if i ∈ step.reads then config.state.slots i else none)
                  (fun i => if i ∈ step.writes then some (values i) else none),
                ⟨config.pos ++ [outcome],
                  putAll discipline.inPlace config.state
                    (step.writes.map fun i => (i, values i)),
                  recorded discipline (opened step more config) config.stores step.writes,
                  opened step more config⟩)
  | .back =>
      match config.frames with
      | [] => none
      | frame :: older =>
          (rollbackTo? inventory frame.mark config.state).map fun restored =>
            (.back frame.pos,
              ⟨frame.pos, empty restored (config.stores.drop frame.storeMark),
                config.stores.take frame.storeMark, older⟩)

/-- Run a list of events, collecting what the machine shows. -/
def exec (body : Body inventory Value Input) (discipline : Discipline inventory) :
    Config inventory Value → List (Event Input) →
      Option (List (Obs inventory Value) × Config inventory Value)
  | config, [] => some ([], config)
  | config, event :: events =>
      match next body discipline config event with
      | none => none
      | some (shown, config') =>
          (exec body discipline config' events).map fun result =>
            (shown :: result.1, result.2)

theorem exec_append_singleton (body : Body inventory Value Input)
    (discipline : Discipline inventory) (config : Config inventory Value)
    (events : List (Event Input)) (event : Event Input) :
    exec body discipline config (events ++ [event]) =
      (exec body discipline config events).bind fun result =>
        (next body discipline result.2 event).map fun step =>
          (result.1 ++ [step.1], step.2) := by
  induction events generalizing config with
  | nil =>
      simp only [List.nil_append, exec, Option.bind_some, List.nil_append]
      cases next body discipline config event <;> rfl
  | cons first events inductionHypothesis =>
      simp only [List.cons_append, exec]
      cases next body discipline config first with
      | none => rfl
      | some step =>
          simp only [inductionHypothesis]
          cases exec body discipline step.2 events with
          | none => rfl
          | some result =>
              simp only [Option.map_some, Option.bind_some]
              cases next body discipline result.2 event <;> rfl

/-- The activation's entry: the root position, the slots head matching left,
empty trails, and no choice point. -/
def entry (slots : DenseEnvironment inventory Value) : Config inventory Value :=
  ⟨[], ⟨slots, []⟩, [], []⟩

omit [DecidableEq Key] in
@[simp] theorem empty_nil (state : State inventory Value) : empty state [] = state := by
  cases state
  simp [empty]


end Machine

/-! ## The trailed and direct disciplines run in lock step -/

section Simulation

variable {Key : Type uKey} [DecidableEq Key] {inventory : Inventory Key}
  {Value : Type uValue} {Input : Type uInput}

/-- Two slot vectors agree on every slot outside `U` and on every slot of `U`
in `stored`. -/
def Agree (U stored : Finset inventory.Slot)
    (trailed direct : DenseEnvironment inventory Value) : Prop :=
  ∀ i, (i ∉ U ∨ i ∈ stored) → trailed i = direct i

/-- The correspondence of the two disciplines at a position: their slots agree
where the path may read them, the direct trail names no slot of `U`, and the
two frame stacks open the same choice points, each restoring corresponding
states. -/
inductive Stack (body : Body inventory Value Input) (U : Finset inventory.Slot) :
    List Bool → State inventory Value → State inventory Value →
      List Frame → List Frame → Prop
  | base {pos : List Bool} {trailed direct : State inventory Value}
      (agree : Agree U (body.defined U pos) trailed.slots direct.slots)
      (clean : Clean U direct) :
      Stack body U pos trailed direct [] []
  | frame {pos : List Bool} {trailed direct restoredTrailed restoredDirect :
        State inventory Value}
      {trailedFrame directFrame : Frame} {trailedOlder directOlder : List Frame}
      (agree : Agree U (body.defined U pos) trailed.slots direct.slots)
      (clean : Clean U direct)
      (samePos : trailedFrame.pos = directFrame.pos)
      (above : ∃ outcome, trailedFrame.pos ++ [outcome] <+: pos)
      (restoresTrailed : rollbackTo? inventory trailedFrame.mark trailed =
        some restoredTrailed)
      (restoresDirect : rollbackTo? inventory directFrame.mark direct =
        some restoredDirect)
      (rest : Stack body U trailedFrame.pos restoredTrailed restoredDirect
        trailedOlder directOlder) :
      Stack body U pos trailed direct (trailedFrame :: trailedOlder)
        (directFrame :: directOlder)

namespace Stack

variable {body : Body inventory Value Input} {U : Finset inventory.Slot}

theorem agree' {pos : List Bool} {trailed direct : State inventory Value}
    {trailedFrames directFrames : List Frame}
    (stack : Stack body U pos trailed direct trailedFrames directFrames) :
    Agree U (body.defined U pos) trailed.slots direct.slots := by
  cases stack with
  | base agree _ => exact agree
  | frame agree _ _ _ _ _ _ => exact agree

theorem clean' {pos : List Bool} {trailed direct : State inventory Value}
    {trailedFrames directFrames : List Frame}
    (stack : Stack body U pos trailed direct trailedFrames directFrames) :
    Clean U direct := by
  cases stack with
  | base _ clean => exact clean
  | frame _ clean _ _ _ _ _ => exact clean

/-- An in-place write of a slot of `U` the path has not stored changes nothing
the correspondence observes. -/
theorem writeInPlace {pos : List Bool} {trailed direct : State inventory Value}
    {trailedFrames directFrames : List Frame}
    (stack : Stack body U pos trailed direct trailedFrames directFrames)
    {update : DenseWrite inventory Value} (inU : update.1 ∈ U)
    (fresh : update.1 ∉ body.defined U pos) :
    Stack body U pos trailed (FirstOccurrenceStores.writeInPlace direct update)
      trailedFrames directFrames := by
  have keepAgree : ∀ {pos : List Bool} {trailed direct : State inventory Value},
      update.1 ∉ body.defined U pos →
      Agree U (body.defined U pos) trailed.slots direct.slots →
      Agree U (body.defined U pos) trailed.slots
        (FirstOccurrenceStores.writeInPlace direct update).slots := by
    intro pos trailed direct fresh agree i observed
    by_cases same : i = update.1
    · subst same
      rcases observed with notInU | stored
      · exact (notInU inU).elim
      · exact (fresh stored).elim
    · simp [FirstOccurrenceStores.writeInPlace, writeDense, same, agree i observed]
  induction stack with
  | base agree clean => exact .base (keepAgree fresh agree) clean
  | @frame pos trailed direct restoredTrailed restoredDirect trailedFrame directFrame
      trailedOlder directOlder agree clean samePos above restoresTrailed
      restoresDirect rest inductionHypothesis =>
      obtain ⟨outcome, prefixed⟩ := above
      have freshAbove : update.1 ∉ body.defined U trailedFrame.pos := fun stored =>
        fresh (body.defined_mono U
          ((List.prefix_append trailedFrame.pos [outcome]).trans prefixed) stored)
      refine .frame (keepAgree fresh agree) clean samePos ⟨outcome, prefixed⟩
        restoresTrailed ?_ (inductionHypothesis freshAbove)
      rw [rollbackTo?_writeInPlace _ clean inU, restoresDirect]
      rfl

theorem putAll_direct {pos : List Bool} {trailed direct : State inventory Value}
    {trailedFrames directFrames : List Frame}
    (stack : Stack body U pos trailed direct trailedFrames directFrames)
    (updates : List (DenseWrite inventory Value))
    (fresh : ∀ update ∈ updates, update.1 ∈ U ∧ update.1 ∉ body.defined U pos) :
    Stack body U pos trailed (FirstOccurrenceStores.putAll U direct updates)
      trailedFrames directFrames := by
  induction updates generalizing direct with
  | nil => exact stack
  | cons update updates inductionHypothesis =>
      have head := fresh update List.mem_cons_self
      have putInPlace : put U direct update =
          FirstOccurrenceStores.writeInPlace direct update := by
        simp [put, head.1]
      rw [FirstOccurrenceStores.putAll, putInPlace]
      exact inductionHypothesis (stack.writeInPlace head.1 head.2)
        fun later member => fresh later (List.mem_cons_of_mem _ member)

end Stack

/-- The trailed and the untrailed discipline are at the same position, with
empty store trails, and correspond there. -/
def Corresponds (body : Body inventory Value Input) (U : Finset inventory.Slot)
    (trailed direct : Config inventory Value) : Prop :=
  trailed.pos = direct.pos ∧ trailed.stores = [] ∧ direct.stores = [] ∧
    Stack body U trailed.pos trailed.state direct.state trailed.frames direct.frames

variable {body : Body inventory Value Input} {U : Finset inventory.Slot}

omit [DecidableEq Key] in
/-- A visited step reads the same values in both disciplines. -/
theorem run_same (firstStores : body.FirstStores U) {pos : List Bool}
    {step : Step inventory Value Input} {next : Bool → Body inventory Value Input}
    (found : body.follow pos = .node step next)
    {trailed direct : DenseEnvironment inventory Value}
    (agree : Agree U (body.defined U pos) trailed direct) (input : Input) :
    step.run trailed input = step.run direct input := by
  apply step.run_congr
  intro i reads
  apply agree i
  by_cases inU : i ∈ U
  · exact .inr ((firstStores pos step next found).1 (Finset.mem_inter.mpr ⟨reads, inU⟩))
  · exact .inl inU

/-- **One event.**  Corresponding configurations take the same event to
corresponding configurations, showing the same thing, or both refuse it. -/
theorem next_corresponds (firstStores : body.FirstStores U)
    {trailed direct : Config inventory Value}
    (corresponds : Corresponds body U trailed direct) (event : Event Input) :
    Option.Rel (fun left right => left.1 = right.1 ∧ Corresponds body U left.2 right.2)
      (next body .trailed trailed event) (next body (.untrailed U) direct event) := by
  obtain ⟨pos, trailedState, trailedStores, trailedFrames⟩ := trailed
  obtain ⟨directPos, directState, directStores, directFrames⟩ := direct
  obtain ⟨samePos, trailedEmpty, directEmpty, stack⟩ := corresponds
  change pos = directPos at samePos
  change trailedStores = [] at trailedEmpty
  change directStores = [] at directEmpty
  subst samePos trailedEmpty directEmpty
  change Stack body U pos trailedState directState trailedFrames directFrames at stack
  cases event with
  | step input more =>
      simp only [next]
      cases found : body.follow pos with
      | stop => exact .none
      | node step next =>
          simp only
          rw [run_same firstStores found stack.agree' input]
          cases ran : step.run directState.slots input with
          | none => exact .none
          | some result =>
              obtain ⟨values, outcome⟩ := result
              have storesFresh : ∀ update ∈ directPart U
                  (step.writes.map fun i => (i, values i)),
                  update.1 ∈ U ∧ update.1 ∉ body.defined U pos := by
                intro update member
                obtain ⟨written, inU⟩ := mem_directPart member
                obtain ⟨i, writes, rfl⟩ := List.mem_map.mp written
                exact ⟨inU, (firstStores _ step next found).2 i writes inU⟩
              have agreeAfter : Agree U (body.defined U (pos ++ [outcome]))
                  (putAll ∅ trailedState (step.writes.map fun i => (i, values i))).slots
                  (putAll U directState (step.writes.map fun i => (i, values i))).slots := by
                intro i observed
                rw [putAll_slots, putAll_slots]
                split
                · rfl
                · next unwritten =>
                    apply stack.agree' i
                    rcases observed with notInU | stored
                    · exact .inl notInU
                    · rw [body.defined_append U found outcome, Finset.mem_union] at stored
                      rcases stored with earlier | now
                      · exact .inr earlier
                      · exact (unwritten (List.mem_toFinset.mp
                          (Finset.mem_inter.mp now).1)).elim
              have extended : pos <+: pos ++ [outcome] := List.prefix_append _ _
              have older : Stack body U (pos ++ [outcome])
                  (putAll ∅ trailedState (step.writes.map fun i => (i, values i)))
                  (putAll U directState (step.writes.map fun i => (i, values i)))
                  trailedFrames directFrames := by
                cases stack with
                | base _ clean => exact .base agreeAfter (clean.putAll _)
                | frame _ clean framePos above restoresTrailed restoresDirect rest =>
                    obtain ⟨frameOutcome, below⟩ := above
                    refine .frame agreeAfter (clean.putAll _) framePos
                      ⟨frameOutcome, below.trans extended⟩ ?_ ?_
                      (rest.putAll_direct _ fun update member =>
                        ⟨(storesFresh update member).1, fun stored =>
                          (storesFresh update member).2
                            (body.defined_mono U
                              ((List.prefix_append _ [frameOutcome]).trans below) stored)⟩)
                    · rw [rollbackTo?_putAll_empty_of_le
                        (mark_le_of_rollbackTo? restoresTrailed)]
                      exact restoresTrailed
                    · rw [rollbackTo?_putAll clean (mark_le_of_rollbackTo? restoresDirect),
                        restoresDirect]
                      rfl
              refine .some ⟨?_, rfl, ?_, ?_, ?_⟩
              · show Obs.visit pos _ _ = Obs.visit pos _ _
                congr 1
                funext i
                by_cases reads : i ∈ step.reads
                · simp only [reads, if_true]
                  apply stack.agree' i
                  by_cases inU : i ∈ U
                  · exact .inr ((firstStores _ step next found).1
                      (Finset.mem_inter.mpr ⟨reads, inU⟩))
                  · exact .inl inU
                · simp [reads]
              · simp [recorded, Discipline.trailed]
              · simp [recorded, Discipline.untrailed]
              · show Stack body U (pos ++ [outcome]) (putAll ∅ _ _) (putAll U _ _)
                  (opened step more _) (opened step more _)
                unfold opened
                split
                · refine .frame agreeAfter (stack.clean'.putAll _) rfl
                    ⟨outcome, List.prefix_refl _⟩ ?_ ?_
                    (stack.putAll_direct _ storesFresh)
                  · rw [putAll_empty, rollbackTo?_run]
                  · rw [rollbackTo?_putAll stack.clean' le_rfl, rollbackTo?_mark]
                    rfl
                · exact older
  | back =>
      simp only [next]
      cases stack with
      | base _ _ => exact .none
      | frame _ _ framePos _ restoresTrailed restoresDirect rest =>
          simp only [restoresTrailed, restoresDirect, Option.map_some, List.drop_nil,
            List.take_nil, empty_nil]
          exact .some ⟨by rw [framePos], framePos, rfl, rfl, rest⟩

theorem rel_bind {α β γ δ : Type*} {R : α → β → Prop} {S : γ → δ → Prop}
    {left : Option α} {right : Option β} (related : Option.Rel R left right)
    {f : α → Option γ} {g : β → Option δ}
    (preserve : ∀ a b, R a b → Option.Rel S (f a) (g b)) :
    Option.Rel S (left.bind f) (right.bind g) := by
  cases related with
  | none => exact .none
  | some same => exact preserve _ _ same

theorem rel_map {α β γ δ : Type*} {R : α → β → Prop} {S : γ → δ → Prop}
    {left : Option α} {right : Option β} (related : Option.Rel R left right)
    {f : α → γ} {g : β → δ} (preserve : ∀ a b, R a b → S (f a) (g b)) :
    Option.Rel S (left.map f) (right.map g) := by
  cases related with
  | none => exact .none
  | some same => exact .some (preserve _ _ same)

theorem exec_cons (discipline : Discipline inventory) (config : Config inventory Value)
    (event : Event Input) (events : List (Event Input)) :
    exec body discipline config (event :: events) =
      (next body discipline config event).bind fun step =>
        (exec body discipline step.2 events).map fun result =>
          (step.1 :: result.1, result.2) := by
  simp only [exec]
  cases next body discipline config event <;> rfl

/-- **Lock step.**  From corresponding configurations, every list of events
drives the trailed and the untrailed discipline to corresponding
configurations with the same observations, or neither accepts it. -/
theorem exec_corresponds (firstStores : body.FirstStores U) :
    ∀ (events : List (Event Input)) {trailed direct : Config inventory Value},
      Corresponds body U trailed direct →
      Option.Rel (fun left right => left.1 = right.1 ∧ Corresponds body U left.2 right.2)
        (exec body .trailed trailed events) (exec body (.untrailed U) direct events)
  | [], _, _, corresponds => .some ⟨rfl, corresponds⟩
  | event :: events, trailed, direct, corresponds => by
      rw [exec_cons, exec_cons]
      refine rel_bind (next_corresponds firstStores corresponds event) ?_
      intro left right same
      refine rel_map (exec_corresponds firstStores events same.2) ?_
      intro leftResult rightResult sameResult
      exact ⟨by rw [same.1, sameResult.1], sameResult.2⟩

theorem map_eq_of_rel {α β γ : Type*} {R : α → β → Prop} {left : Option α}
    {right : Option β} (related : Option.Rel R left right) {f : α → γ} {g : β → γ}
    (same : ∀ a b, R a b → f a = g b) : left.map f = right.map g := by
  cases related with
  | none => rfl
  | some agree => exact congrArg some (same _ _ agree)

theorem entry_corresponds (slots : DenseEnvironment inventory Value) :
    Corresponds body U (entry slots) (entry slots) :=
  ⟨rfl, rfl, rfl, .base (fun _ _ => rfl) (fun _ member => by cases member)⟩

/-- **Observational equivalence without the store trail.**  For a body meeting
the first-occurrence condition, the machine that writes the slots of `U` in
place and never undoes those writes, and the machine that trails every write,
accept the same event lists and show the same observations on them.  The
reads cannot tell the disciplines apart; a reader of the whole slot vector can
(`Canary.untrailed_keeps_stale_slot`). -/
theorem exec_observations_eq_untrailed (firstStores : body.FirstStores U)
    (slots : DenseEnvironment inventory Value) (events : List (Event Input)) :
    (exec body .trailed (entry slots) events).map Prod.fst =
      (exec body (.untrailed U) (entry slots) events).map Prod.fst :=
  map_eq_of_rel (exec_corresponds firstStores events (entry_corresponds slots))
    fun _ _ same => same.1

end Simulation

/-! ## What a read sees -/

section Reads

variable {Key : Type uKey} [DecidableEq Key] {inventory : Inventory Key}
  {Value : Type uValue} {Input : Type uInput}
  {body : Body inventory Value Input} {U : Finset inventory.Slot}

/-- The frame stack and the store trail along the path: each choice point
opens strictly above the next newer one, the newest strictly above the current
position; its store mark lies within the store trail, and every entry beyond it
is a slot of `U` the path had not stored at the choice point. -/
inductive Trailed (body : Body inventory Value Input) (U : Finset inventory.Slot) :
    List Bool → List inventory.Slot → List Frame → Prop
  | nil (pos : List Bool) (stores : List inventory.Slot) : Trailed body U pos stores []
  | cons {pos : List Bool} {stores : List inventory.Slot} {frame : Frame}
      {older : List Frame}
      (above : ∃ outcome, frame.pos ++ [outcome] <+: pos)
      (marked : frame.storeMark ≤ stores.length)
      (later : ∀ i ∈ stores.drop frame.storeMark, i ∈ U ∧ i ∉ body.defined U frame.pos)
      (rest : Trailed body U frame.pos (stores.take frame.storeMark) older) :
      Trailed body U pos stores (frame :: older)

theorem next_step_inv {discipline : Discipline inventory}
    {config config' : Config inventory Value} {input : Input} {more : Bool}
    {shown : Obs inventory Value}
    (stepped : next body discipline config (.step input more) = some (shown, config')) :
    ∃ step successor values outcome,
      body.follow config.pos = .node step successor ∧
      step.run config.state.slots input = some (values, outcome) ∧
      shown = .visit config.pos
        (fun i => if i ∈ step.reads then config.state.slots i else none)
        (fun i => if i ∈ step.writes then some (values i) else none) ∧
      config' = ⟨config.pos ++ [outcome],
        putAll discipline.inPlace config.state (step.writes.map fun i => (i, values i)),
        recorded discipline (opened step more config) config.stores step.writes,
        opened step more config⟩ := by
  simp only [next] at stepped
  split at stepped
  · cases stepped
  · next step successor found =>
      split at stepped
      · cases stepped
      · next values outcome ran =>
          cases stepped
          exact ⟨step, successor, values, outcome, found, ran, rfl, rfl⟩

theorem next_back_inv {discipline : Discipline inventory}
    {config config' : Config inventory Value} {shown : Obs inventory Value}
    (stepped : next body discipline config .back = some (shown, config')) :
    ∃ frame older restored, config.frames = frame :: older ∧
      rollbackTo? inventory frame.mark config.state = some restored ∧
      shown = .back frame.pos ∧
      config' = ⟨frame.pos, empty restored (config.stores.drop frame.storeMark),
        config.stores.take frame.storeMark, older⟩ := by
  simp only [next] at stepped
  split at stepped
  · cases stepped
  · next frame older frames =>
      obtain ⟨restored, restores, same⟩ := Option.map_eq_some_iff.mp stepped
      cases same
      exact ⟨frame, older, restored, frames, restores, rfl, rfl⟩

theorem exec_snoc_inv {discipline : Discipline inventory}
    {config config' : Config inventory Value} {events : List (Event Input)}
    {event : Event Input} {shown : List (Obs inventory Value)}
    (ran : exec body discipline config (events ++ [event]) = some (shown, config')) :
    ∃ shownBefore middle last,
      exec body discipline config events = some (shownBefore, middle) ∧
      next body discipline middle event = some (last, config') ∧
      shown = shownBefore ++ [last] := by
  rw [exec_append_singleton] at ran
  obtain ⟨⟨shownBefore, middle⟩, before, after⟩ := Option.bind_eq_some_iff.mp ran
  obtain ⟨⟨last, final⟩, stepped, same⟩ := Option.map_eq_some_iff.mp after
  cases same
  exact ⟨shownBefore, middle, last, before, stepped, rfl⟩

omit [DecidableEq Key] in
/-- The store trail grows by some of the step's in-place writes, and only while
a choice point is live. -/
theorem recorded_eq_append (discipline : Discipline inventory) (frames : List Frame)
    (stores writes : List inventory.Slot) :
    ∃ extra, recorded discipline frames stores writes = stores ++ extra ∧
      (∀ i ∈ extra, i ∈ writes ∧ i ∈ discipline.inPlace) ∧
      (frames = [] → extra = []) := by
  unfold recorded
  split
  · next trails =>
      exact ⟨_, rfl, fun i member => by simpa using member,
        fun empty => (trails.2 empty).elim⟩
  · exact ⟨[], by simp, (fun _ member => by cases member), fun _ => rfl⟩

omit [DecidableEq Key] in
/-- A step keeps the invariant under a discipline writing `U` in place. -/
theorem Trailed.step (storesFresh : body.StoresFresh U) {discipline : Discipline inventory}
    (inPlace : discipline.inPlace = U) {config : Config inventory Value}
    (trailed : Trailed body U config.pos config.stores config.frames)
    {step : Step inventory Value Input} {successor : Bool → Body inventory Value Input}
    (found : body.follow config.pos = .node step successor) (more outcome : Bool) :
    Trailed body U (config.pos ++ [outcome])
      (recorded discipline (opened step more config) config.stores step.writes)
      (opened step more config) := by
  obtain ⟨pos, state, stores, frames⟩ := config
  change Trailed body U pos stores frames at trailed
  change body.follow pos = _ at found
  obtain ⟨extra, recordedEq, extraWritten, extraOnlyLive⟩ :=
    recorded_eq_append discipline (opened step more ⟨pos, state, stores, frames⟩) stores
      step.writes
  change Trailed body U (pos ++ [outcome]) _ _
  rw [recordedEq]
  have fresh : ∀ i ∈ extra, i ∈ U ∧ i ∉ body.defined U pos := by
    intro i member
    obtain ⟨written, direct⟩ := extraWritten i member
    rw [inPlace] at direct
    exact ⟨direct, storesFresh _ step successor found i written direct⟩
  have extended : pos <+: pos ++ [outcome] := List.prefix_append _ _
  unfold opened at extraOnlyLive ⊢
  split
  · refine .cons ⟨outcome, List.prefix_refl _⟩ (by simp) ?_ ?_
    · intro i member
      rw [List.drop_left] at member
      exact fresh i member
    · rw [List.take_left]
      exact trailed
  · next noChoice =>
      rw [if_neg noChoice] at extraOnlyLive
      cases trailed with
      | nil => exact .nil _ _
      | @cons _ _ frame older above marked later rest =>
          obtain ⟨frameOutcome, below⟩ := above
          refine .cons ⟨frameOutcome, below.trans extended⟩ (by simp; omega) ?_ ?_
          · intro i member
            rw [List.drop_append_of_le_length marked, List.mem_append] at member
            rcases member with old | new
            · exact later i old
            · exact ⟨(fresh i new).1, fun stored => (fresh i new).2
                (body.defined_mono U ((List.prefix_append _ [frameOutcome]).trans below)
                  stored)⟩
          · rw [List.take_append_of_le_length marked]
            exact rest

/-- **The value of a stored slot is its most recent store.**  Under either
discipline that writes `U` in place, with or without the store trail, in every
configuration reachable from the entry a slot of `U` that the path has stored
holds the value written by the most recent visit of its store, the unique step
above the position that writes it: the observations contain that visit and no
later visit of its position.  Along the way the undo trail names no slot of `U`
and the frames and store trail keep `Trailed`. -/
theorem inPlace_most_recent_store (storesFresh : body.StoresFresh U)
    (slots : DenseEnvironment inventory Value) {discipline : Discipline inventory}
    (inPlace : discipline.inPlace = U) :
    ∀ (events : List (Event Input)) {shown : List (Obs inventory Value)}
      {config : Config inventory Value},
      exec body discipline (entry slots) events = some (shown, config) →
      Clean U config.state ∧ Trailed body U config.pos config.stores config.frames ∧
      ∀ i ∈ U, i ∈ body.defined U config.pos →
        ∃ pre above seen wrote post,
          shown = pre ++ Obs.visit above seen wrote :: post ∧
          (∃ outcome, above ++ [outcome] <+: config.pos) ∧ body.WritesAt above i ∧
          (∀ later ∈ post, later.visited ≠ some above) ∧
          ∃ value, wrote i = some value ∧ config.state.slots i = some value := by
  intro events
  induction events using List.reverseRecOn with
  | nil =>
      intro shown config ran
      simp only [exec, Option.some.injEq, Prod.mk.injEq] at ran
      obtain ⟨rfl, rfl⟩ := ran
      refine ⟨fun _ member => by simp [entry] at member, Trailed.nil _ _, ?_⟩
      intro i _ stored
      simp [entry, Body.defined] at stored
  | append_singleton events event inductionHypothesis =>
      intro shown config' ran
      obtain ⟨shownBefore, config, last, before, stepped, rfl⟩ := exec_snoc_inv ran
      obtain ⟨clean, trailed, recent⟩ := inductionHypothesis before
      cases event with
      | step input more =>
          obtain ⟨step, successor, values, outcome, found, _, lastEq, rfl⟩ :=
            next_step_inv stepped
          refine ⟨by rw [inPlace]; exact clean.putAll _,
            trailed.step storesFresh inPlace found more outcome, ?_⟩
          intro i inU stored
          dsimp only at stored ⊢
          simp only [putAll_slots]
          by_cases written : i ∈ step.writes
          · refine ⟨shownBefore, config.pos, _, _, [], by rw [lastEq],
              ⟨outcome, List.prefix_refl _⟩, ⟨step, successor, found, written⟩, ?_,
              values i, by simp [written], by simp [written]⟩
            intro later member
            cases member
          · have earlier : i ∈ body.defined U config.pos := by
              rw [body.defined_append U found outcome, Finset.mem_union] at stored
              rcases stored with earlier | now
              · exact earlier
              · exact (written (List.mem_toFinset.mp (Finset.mem_inter.mp now).1)).elim
            obtain ⟨pre, above, seen, wrote, post, rfl, ⟨aboveOutcome, below⟩, writes,
              noLater, value, wroteValue, holds⟩ := recent i inU earlier
            refine ⟨pre, above, seen, wrote, post ++ [last], by simp,
              ⟨aboveOutcome, below.trans (List.prefix_append _ _)⟩, writes, ?_, value,
              wroteValue, by simp [written, holds]⟩
            intro later member
            rcases List.mem_append.mp member with old | new
            · exact noLater later old
            · rw [List.mem_singleton] at new
              subst new
              rw [lastEq]
              intro same
              simp only [Obs.visited, Option.some.injEq] at same
              have shorter := below.length_le
              rw [same] at shorter
              simp only [List.length_append, List.length_singleton] at shorter
              omega
      | back =>
          obtain ⟨frame, older, restored, frames, restores, rfl, rfl⟩ :=
            next_back_inv stepped
          obtain ⟨cleanRestored, kept⟩ := rollbackTo?_clean clean restores
          rw [frames] at trailed
          cases trailed with
          | cons frameAbove _ later rest =>
              obtain ⟨frameOutcome, frameBelow⟩ := frameAbove
              refine ⟨cleanRestored, rest, ?_⟩
              intro i inU stored
              have storedBelow : i ∈ body.defined U config.pos :=
                body.defined_mono U ((List.prefix_append _ _).trans frameBelow) stored
              obtain ⟨pre, above, seen, wrote, post, rfl, ⟨aboveOutcome, below⟩, writes,
                noLater, value, wroteValue, holds⟩ := recent i inU storedBelow
              obtain ⟨_, above', aboveOutcome', below', writes'⟩ :=
                (Body.mem_defined_iff U body frame.pos).mp stored
              have same : above' = above :=
                storesFresh.writesAt_unique inU
                  (below'.trans ((List.prefix_append _ _).trans frameBelow)) below
                  writes' writes
              subst same
              refine ⟨pre, above', seen, wrote, post ++ [.back frame.pos], by simp,
                ⟨aboveOutcome', below'⟩, writes, ?_, value, wroteValue, ?_⟩
              · intro later member
                rcases List.mem_append.mp member with old | new
                · exact noLater later old
                · rw [List.mem_singleton] at new
                  subst new
                  simp [Obs.visited]
              · have notEmptied : i ∉ config.stores.drop frame.storeMark :=
                  fun emptied => (later i emptied).2 stored
                show (empty restored (config.stores.drop frame.storeMark)).slots i =
                  some value
                simp only [empty, notEmptied, if_false]
                rw [kept i inU, holds]

theorem rel_some_inv {α β : Type*} {R : α → β → Prop} {a : α} {right : Option β}
    (related : Option.Rel R (some a) right) : ∃ b, right = some b ∧ R a b := by
  cases related with
  | some same => exact ⟨_, rfl, same⟩

theorem rel_some_inv_right {α β : Type*} {R : α → β → Prop} {left : Option α} {b : β}
    (related : Option.Rel R left (some b)) : ∃ a, left = some a ∧ R a b := by
  cases related with
  | some same => exact ⟨_, rfl, same⟩

/-- The same holds of the trailed discipline, which it matches slot for slot
where the path may read. -/
theorem trailed_most_recent_store (firstStores : body.FirstStores U)
    (slots : DenseEnvironment inventory Value) (events : List (Event Input))
    {shown : List (Obs inventory Value)} {config : Config inventory Value}
    (ran : exec body .trailed (entry slots) events = some (shown, config)) :
    ∀ i ∈ U, i ∈ body.defined U config.pos →
      ∃ pre above seen wrote post,
        shown = pre ++ Obs.visit above seen wrote :: post ∧
        (∃ outcome, above ++ [outcome] <+: config.pos) ∧ body.WritesAt above i ∧
        (∀ later ∈ post, later.visited ≠ some above) ∧
        ∃ value, wrote i = some value ∧ config.state.slots i = some value := by
  intro i inU stored
  have related := exec_corresponds firstStores events (entry_corresponds slots)
  rw [ran] at related
  obtain ⟨⟨shownDirect, configDirect⟩, directRan, sameShown, samePos, _, _, stack⟩ :=
    rel_some_inv related
  change config.pos = configDirect.pos at samePos
  change shown = shownDirect at sameShown
  subst sameShown
  rw [samePos] at stored ⊢
  obtain ⟨_, _, recent⟩ := inPlace_most_recent_store firstStores.storesFresh slots rfl
    events directRan
  obtain ⟨pre, above, seen, wrote, post, shownEq, below, writes, noLater, value,
    wroteValue, holds⟩ := recent i inU stored
  refine ⟨pre, above, seen, wrote, post, shownEq, below, writes, noLater, value,
    wroteValue, ?_⟩
  rw [stack.agree' i (.inr (samePos ▸ stored)), holds]

/-- **What a reader may inspect.**  Any function of the slot vector that looks
only at slots outside `U` and at slots of `U` the current path has stored takes
the same value under the trailed and the untrailed discipline, in every
configuration they reach.  A reader that inspects another slot of `U` has no
such guarantee (`Canary.untrailed_keeps_stale_slot`). -/
theorem restricted_reader_agrees {Result : Type*} (firstStores : body.FirstStores U)
    (slots : DenseEnvironment inventory Value) (events : List (Event Input))
    {shownTrailed shownDirect : List (Obs inventory Value)}
    {trailed direct : Config inventory Value}
    (ranTrailed : exec body .trailed (entry slots) events = some (shownTrailed, trailed))
    (ranDirect : exec body (.untrailed U) (entry slots) events =
      some (shownDirect, direct))
    (read : DenseEnvironment inventory Value → Result)
    (restricted : ∀ first second : DenseEnvironment inventory Value,
      (∀ i, (i ∉ U ∨ i ∈ body.defined U trailed.pos) → first i = second i) →
        read first = read second) :
    trailed.pos = direct.pos ∧ read trailed.state.slots = read direct.state.slots := by
  have related := exec_corresponds firstStores events (entry_corresponds slots)
  rw [ranTrailed, ranDirect] at related
  cases related with
  | some same =>
      obtain ⟨_, samePos, _, _, stack⟩ := same
      exact ⟨samePos, restricted _ _ stack.agree'⟩

theorem exec_take_drop {discipline : Discipline inventory} :
    ∀ (events : List (Event Input)) {config config' : Config inventory Value}
      {shown : List (Obs inventory Value)},
      exec body discipline config events = some (shown, config') →
      ∀ count, ∃ middle,
        exec body discipline config (events.take count) = some (shown.take count, middle) ∧
        exec body discipline middle (events.drop count) = some (shown.drop count, config')
  | [], config, config', shown, ran, count => by
      simp only [exec, Option.some.injEq, Prod.mk.injEq] at ran
      obtain ⟨rfl, rfl⟩ := ran
      exact ⟨config, by simp [exec], by simp [exec]⟩
  | event :: events, config, config', shown, ran, count => by
      rw [exec_cons] at ran
      obtain ⟨⟨last, middle⟩, stepped, after⟩ := Option.bind_eq_some_iff.mp ran
      obtain ⟨⟨rest, final⟩, restRan, same⟩ := Option.map_eq_some_iff.mp after
      simp only [Prod.mk.injEq] at same
      obtain ⟨rfl, rfl⟩ := same
      cases count with
      | zero =>
          refine ⟨config, by simp [exec], ?_⟩
          simp only [List.drop_zero]
          rw [exec_cons, stepped, Option.bind_some, restRan]
          rfl
      | succ count =>
          obtain ⟨between, before, after⟩ := exec_take_drop events restRan count
          refine ⟨between, ?_, by simpa using after⟩
          rw [List.take_succ_cons, exec_cons, stepped, Option.bind_some, before]
          rfl

/-- **Every read sees its most recent store.**  In the trailed discipline and in
every discipline writing `U` in place, whenever a visited step reads a slot of
`U`, the observations before it contain a visit of that slot's store above the
step's position, no later visit of that store position follows, and the value
that visit wrote is the value the read sees. -/
theorem read_sees_most_recent_store (firstStores : body.FirstStores U)
    (slots : DenseEnvironment inventory Value) {discipline : Discipline inventory}
    (known : discipline = .trailed ∨ discipline.inPlace = U) (events : List (Event Input))
    {shown : List (Obs inventory Value)} {config : Config inventory Value}
    (ran : exec body discipline (entry slots) events = some (shown, config))
    {pre post : List (Obs inventory Value)} {pos : List Bool}
    {seen wrote : DenseEnvironment inventory Value}
    (visit : shown = pre ++ Obs.visit pos seen wrote :: post)
    {step : Step inventory Value Input} {successor : Bool → Body inventory Value Input}
    (found : body.follow pos = .node step successor)
    {i : inventory.Slot} (inU : i ∈ U) (reads : i ∈ step.reads) :
    ∃ earlier above seenAbove wroteAbove between,
      pre = earlier ++ Obs.visit above seenAbove wroteAbove :: between ∧
      (∃ outcome, above ++ [outcome] <+: pos) ∧ body.WritesAt above i ∧
      (∀ later ∈ between, later.visited ≠ some above) ∧
      ∃ value, wroteAbove i = some value ∧ seen i = some value := by
  obtain ⟨middle, before, after⟩ := exec_take_drop events ran pre.length
  have shownBefore : shown.take pre.length = pre := by simp [visit]
  have shownAfter : shown.drop pre.length = Obs.visit pos seen wrote :: post := by
    simp [visit]
  rw [shownBefore] at before
  rw [shownAfter] at after
  cases remaining : events.drop pre.length with
  | nil =>
      rw [remaining] at after
      simp [exec] at after
  | cons event rest =>
      rw [remaining, exec_cons] at after
      obtain ⟨⟨last, following⟩, stepped, afterStep⟩ := Option.bind_eq_some_iff.mp after
      obtain ⟨⟨restShown, final⟩, _, same⟩ := Option.map_eq_some_iff.mp afterStep
      simp only [Prod.mk.injEq, List.cons.injEq] at same
      obtain ⟨⟨rfl, _⟩, _⟩ := same
      cases event with
      | back =>
          obtain ⟨_, _, _, _, _, lastEq, _⟩ := next_back_inv stepped
          cases lastEq
      | step input more =>
          obtain ⟨step', successor', values, outcome, found', _, lastEq, _⟩ :=
            next_step_inv stepped
          simp only [Obs.visit.injEq] at lastEq
          obtain ⟨rfl, rfl, _⟩ := lastEq
          rw [found] at found'
          cases found'
          have stored : i ∈ body.defined U middle.pos :=
            (firstStores _ step successor found).1 (Finset.mem_inter.mpr ⟨reads, inU⟩)
          have recent : ∀ i ∈ U, i ∈ body.defined U middle.pos →
              ∃ pre' above seen' wrote' post',
                pre = pre' ++ Obs.visit above seen' wrote' :: post' ∧
                (∃ outcome, above ++ [outcome] <+: middle.pos) ∧ body.WritesAt above i ∧
                (∀ later ∈ post', later.visited ≠ some above) ∧
                ∃ value, wrote' i = some value ∧ middle.state.slots i = some value := by
            rcases known with rfl | inPlace
            · exact trailed_most_recent_store firstStores slots _ before
            · exact (inPlace_most_recent_store firstStores.storesFresh slots inPlace _
                before).2.2
          obtain ⟨earlier, above, seenAbove, wroteAbove, between, preEq, below, writes,
            noLater, value, wroteValue, holds⟩ := recent i inU stored
          exact ⟨earlier, above, seenAbove, wroteAbove, between, preEq, below, writes,
            noLater, value, wroteValue, by simp [reads, holds]⟩

end Reads

/-! ## The store trail -/

section StoreTrail

variable {Key : Type uKey} [DecidableEq Key] {inventory : Inventory Key}
  {Value : Type uValue} {Input : Type uInput}
  {body : Body inventory Value Input} {U : Finset inventory.Slot}

/-- In-place writes of slots of `U` leave the undo trail as it is. -/
theorem putAll_inPlace_trail {state : State inventory Value}
    {updates : List (DenseWrite inventory Value)}
    (inU : ∀ update ∈ updates, update.1 ∈ U) :
    (putAll U state updates).trail = state.trail := by
  induction updates generalizing state with
  | nil => rfl
  | cons update updates inductionHypothesis =>
      have putInPlace : put U state update = writeInPlace state update := by
        simp [put, inU update List.mem_cons_self]
      rw [putAll, putInPlace,
        inductionHypothesis fun later member => inU later (List.mem_cons_of_mem _ member)]
      rfl

omit [DecidableEq Key] in
theorem directPart_map (writes : List inventory.Slot) (values : inventory.Slot → Value) :
    directPart U (writes.map fun i => (i, values i)) =
      (writes.filter fun i => decide (i ∈ U)).map fun i => (i, values i) := by
  simp [directPart, List.filter_map, Function.comp_def]

/-- Emptying the slots written in place undoes those writes when the slots were
empty. -/
theorem empty_putAll_filter {restored : State inventory Value}
    {writes : List inventory.Slot} {values : inventory.Slot → Value}
    (wereEmpty : ∀ i ∈ writes, i ∈ U → restored.slots i = none)
    (emptied : List inventory.Slot) :
    empty (putAll U restored
        ((writes.filter fun i => decide (i ∈ U)).map fun i => (i, values i)))
      (emptied ++ writes.filter fun i => decide (i ∈ U)) =
      empty restored emptied := by
  have trailSame := putAll_inPlace_trail (U := U) (state := restored)
    (updates := (writes.filter fun i => decide (i ∈ U)).map fun i => (i, values i))
    (by
      intro update member
      obtain ⟨i, filtered, rfl⟩ := List.mem_map.mp member
      simpa using (List.mem_filter.mp filtered).2)
  unfold empty
  rw [trailSame]
  congr 1
  funext j
  rw [putAll_slots]
  by_cases emptiedHere : j ∈ emptied
  · simp [emptiedHere]
  · by_cases written : j ∈ writes.filter fun i => decide (i ∈ U)
    · obtain ⟨inWrites, inU⟩ := List.mem_filter.mp written
      simp [emptiedHere, written, wereEmpty j inWrites (by simpa using inU)]
    · simp [emptiedHere, written]

/-- The store-trailed discipline beside the trailed one at a position: the same
slots, an undo trail on the store-trailed side naming no slot of `U`, the slots
of `U` the path has not stored empty, and the two frame stacks opening the same
choice points, each restoring mirrored states; beyond a frame's store mark the
store trail names only slots of `U` the path had not stored at the frame. -/
inductive Mirror (body : Body inventory Value Input) (U : Finset inventory.Slot) :
    List Bool → State inventory Value → State inventory Value →
      List inventory.Slot → List Frame → List Frame → Prop
  | base {pos : List Bool} {trailed direct : State inventory Value}
      {stores : List inventory.Slot}
      (same : trailed.slots = direct.slots) (clean : Clean U direct)
      (unstored : ∀ i ∈ U, i ∉ body.defined U pos → trailed.slots i = none) :
      Mirror body U pos trailed direct stores [] []
  | frame {pos : List Bool} {trailed direct restoredTrailed restoredDirect :
        State inventory Value} {stores : List inventory.Slot}
      {trailedFrame directFrame : Frame} {trailedOlder directOlder : List Frame}
      (same : trailed.slots = direct.slots) (clean : Clean U direct)
      (unstored : ∀ i ∈ U, i ∉ body.defined U pos → trailed.slots i = none)
      (samePos : trailedFrame.pos = directFrame.pos)
      (above : ∃ outcome, trailedFrame.pos ++ [outcome] <+: pos)
      (marked : directFrame.storeMark ≤ stores.length)
      (later : ∀ i ∈ stores.drop directFrame.storeMark,
        i ∈ U ∧ i ∉ body.defined U trailedFrame.pos)
      (restoresTrailed : rollbackTo? inventory trailedFrame.mark trailed =
        some restoredTrailed)
      (restoresDirect : rollbackTo? inventory directFrame.mark direct =
        some restoredDirect)
      (rest : Mirror body U trailedFrame.pos restoredTrailed
        (empty restoredDirect (stores.drop directFrame.storeMark))
        (stores.take directFrame.storeMark) trailedOlder directOlder) :
      Mirror body U pos trailed direct stores (trailedFrame :: trailedOlder)
        (directFrame :: directOlder)

namespace Mirror

theorem same' {pos : List Bool} {trailed direct : State inventory Value}
    {stores : List inventory.Slot} {trailedFrames directFrames : List Frame}
    (mirror : Mirror body U pos trailed direct stores trailedFrames directFrames) :
    trailed.slots = direct.slots := by
  cases mirror with
  | base same _ _ => exact same
  | frame same _ _ _ _ _ _ _ _ _ => exact same

theorem clean' {pos : List Bool} {trailed direct : State inventory Value}
    {stores : List inventory.Slot} {trailedFrames directFrames : List Frame}
    (mirror : Mirror body U pos trailed direct stores trailedFrames directFrames) :
    Clean U direct := by
  cases mirror with
  | base _ clean _ => exact clean
  | frame _ clean _ _ _ _ _ _ _ _ => exact clean

theorem unstored' {pos : List Bool} {trailed direct : State inventory Value}
    {stores : List inventory.Slot} {trailedFrames directFrames : List Frame}
    (mirror : Mirror body U pos trailed direct stores trailedFrames directFrames) :
    ∀ i ∈ U, i ∉ body.defined U pos → trailed.slots i = none := by
  cases mirror with
  | base _ _ unstored => exact unstored
  | frame _ _ unstored _ _ _ _ _ _ _ => exact unstored

/-- A step keeps the two disciplines mirrored. -/
theorem step (storesFresh : body.StoresFresh U) {pos : List Bool}
    {trailed direct : State inventory Value} {stores : List inventory.Slot}
    {trailedFrames directFrames : List Frame}
    (mirror : Mirror body U pos trailed direct stores trailedFrames directFrames)
    {step : Step inventory Value Input} {successor : Bool → Body inventory Value Input}
    (found : body.follow pos = .node step successor) (values : inventory.Slot → Value)
    (outcome more : Bool) :
    Mirror body U (pos ++ [outcome])
      (putAll ∅ trailed (step.writes.map fun i => (i, values i)))
      (putAll U direct (step.writes.map fun i => (i, values i)))
      (recorded (.storeTrailed U)
        (if step.choice && more then ⟨pos, mark direct, stores.length⟩ :: directFrames
          else directFrames) stores step.writes)
      (if step.choice && more then ⟨pos, mark trailed, 0⟩ :: trailedFrames
        else trailedFrames)
      (if step.choice && more then ⟨pos, mark direct, stores.length⟩ :: directFrames
        else directFrames) := by
  have fresh : ∀ i ∈ step.writes.filter (fun i => decide (i ∈ U)),
      i ∈ U ∧ i ∉ body.defined U pos := by
    intro i member
    obtain ⟨written, inU⟩ := List.mem_filter.mp member
    have direct : i ∈ U := by simpa using inU
    exact ⟨direct, storesFresh pos step successor found i written direct⟩
  have wereEmpty : ∀ i ∈ step.writes, i ∈ U → direct.slots i = none := by
    intro i written inU
    rw [← mirror.same']
    exact mirror.unstored' i inU (storesFresh pos step successor found i written inU)
  have sameAfter : (putAll ∅ trailed (step.writes.map fun i => (i, values i))).slots =
      (putAll U direct (step.writes.map fun i => (i, values i))).slots := by
    funext i
    rw [putAll_slots, putAll_slots, mirror.same']
  have unstoredAfter : ∀ i ∈ U, i ∉ body.defined U (pos ++ [outcome]) →
      (putAll ∅ trailed (step.writes.map fun i => (i, values i))).slots i = none := by
    intro i inU notStored
    rw [body.defined_append U found outcome, Finset.mem_union, not_or] at notStored
    have unwritten : i ∉ step.writes := fun written =>
      notStored.2 (Finset.mem_inter.mpr ⟨List.mem_toFinset.mpr written, inU⟩)
    rw [putAll_slots, if_neg unwritten]
    exact mirror.unstored' i inU notStored.1
  have cleanAfter := mirror.clean'.putAll (step.writes.map fun i => (i, values i))
  have extended : pos <+: pos ++ [outcome] := List.prefix_append _ _
  have undone : empty (putAll U direct (directPart U (step.writes.map fun i =>
      (i, values i)))) (step.writes.filter fun i => decide (i ∈ U)) = direct := by
    rw [directPart_map]
    have := empty_putAll_filter (U := U) (restored := direct) (values := values)
      wereEmpty []
    simpa using this
  split
  · next pushes =>
      have recordedEq : recorded (.storeTrailed U)
          (⟨pos, mark direct, stores.length⟩ :: directFrames) stores step.writes =
          stores ++ step.writes.filter fun i => decide (i ∈ U) := by
        unfold recorded
        rw [if_pos ⟨rfl, List.cons_ne_nil _ _⟩]
        rfl
      rw [recordedEq]
      refine Mirror.frame (restoredTrailed := trailed)
        (restoredDirect := putAll U direct (directPart U (step.writes.map fun i =>
          (i, values i))))
        sameAfter cleanAfter unstoredAfter rfl ⟨outcome, List.prefix_refl _⟩
        (by simp) ?_ ?_ ?_ ?_
      · intro i member
        rw [List.drop_left] at member
        exact fresh i member
      · rw [putAll_empty, rollbackTo?_run]
      · rw [rollbackTo?_putAll mirror.clean' le_rfl, rollbackTo?_mark]
        rfl
      · rw [List.drop_left, List.take_left, undone]
        exact mirror
  · cases mirror with
    | base same clean unstored =>
        have recordedEq : recorded (.storeTrailed U) [] stores step.writes = stores := by
          simp [recorded]
        rw [recordedEq]
        exact .base sameAfter cleanAfter unstoredAfter
    | @frame _ _ _ restoredTrailed restoredDirect _ trailedFrame directFrame trailedOlder
        directOlder same clean unstored samePos above marked later restoresTrailed
        restoresDirect rest =>
        have recordedEq : recorded (.storeTrailed U) (directFrame :: directOlder) stores
            step.writes = stores ++ step.writes.filter fun i => decide (i ∈ U) := by
          unfold recorded
          rw [if_pos ⟨rfl, List.cons_ne_nil _ _⟩]
          rfl
        rw [recordedEq]
        obtain ⟨frameOutcome, below⟩ := above
        have restoredEmpty : ∀ i ∈ step.writes, i ∈ U → restoredDirect.slots i = none := by
          intro i written inU
          rw [(rollbackTo?_clean clean restoresDirect).2 i inU]
          exact wereEmpty i written inU
        refine Mirror.frame (restoredTrailed := restoredTrailed)
          (restoredDirect := putAll U restoredDirect (directPart U (step.writes.map fun i =>
            (i, values i))))
          sameAfter cleanAfter unstoredAfter samePos
          ⟨frameOutcome, below.trans extended⟩ (by simp; omega) ?_ ?_ ?_ ?_
        · intro i member
          rw [List.drop_append_of_le_length marked, List.mem_append] at member
          rcases member with old | new
          · exact later i old
          · exact ⟨(fresh i new).1, fun stored => (fresh i new).2
              (body.defined_mono U ((List.prefix_append _ [frameOutcome]).trans below)
                stored)⟩
        · rw [rollbackTo?_putAll_empty_of_le (mark_le_of_rollbackTo? restoresTrailed)]
          exact restoresTrailed
        · rw [rollbackTo?_putAll clean (mark_le_of_rollbackTo? restoresDirect),
            restoresDirect]
          rfl
        · rw [List.drop_append_of_le_length marked, List.take_append_of_le_length marked,
            directPart_map, empty_putAll_filter restoredEmpty]
          exact rest

end Mirror

/-- The two disciplines at the same position, the trailed one without a store
trail, mirrored there. -/
def Mirrors (body : Body inventory Value Input) (U : Finset inventory.Slot)
    (trailed direct : Config inventory Value) : Prop :=
  trailed.pos = direct.pos ∧ trailed.stores = [] ∧
    Mirror body U trailed.pos trailed.state direct.state direct.stores trailed.frames
      direct.frames

/-- **One event.**  Mirrored configurations take the same event to mirrored
configurations, showing the same thing, or both refuse it. -/
theorem next_mirrors (storesFresh : body.StoresFresh U)
    {trailed direct : Config inventory Value}
    (mirrors : Mirrors body U trailed direct) (event : Event Input) :
    Option.Rel (fun left right => left.1 = right.1 ∧ Mirrors body U left.2 right.2)
      (next body .trailed trailed event) (next body (.storeTrailed U) direct event) := by
  obtain ⟨pos, trailedState, trailedStores, trailedFrames⟩ := trailed
  obtain ⟨directPos, directState, directStores, directFrames⟩ := direct
  obtain ⟨samePos, trailedEmpty, mirror⟩ := mirrors
  change pos = directPos at samePos
  change trailedStores = [] at trailedEmpty
  subst samePos trailedEmpty
  change Mirror body U pos trailedState directState directStores trailedFrames
    directFrames at mirror
  cases event with
  | step input more =>
      simp only [next]
      cases found : body.follow pos with
      | stop => exact .none
      | node step successor =>
          simp only
          rw [mirror.same']
          cases ran : step.run directState.slots input with
          | none => exact .none
          | some result =>
              obtain ⟨values, outcome⟩ := result
              refine .some ⟨rfl, rfl, ?_, ?_⟩
              · simp [recorded, Discipline.trailed]
              · exact mirror.step storesFresh found values outcome more
  | back =>
      simp only [next]
      cases mirror with
      | base _ _ _ => exact .none
      | frame _ _ _ framePos _ _ _ restoresTrailed restoresDirect rest =>
          simp only [restoresTrailed, restoresDirect, Option.map_some, List.drop_nil,
            List.take_nil, empty_nil]
          exact .some ⟨by rw [framePos], framePos, rfl, rest⟩

/-- **Lock step.**  From mirrored configurations, every list of events drives
the trailed and the store-trailed discipline to mirrored configurations with
the same observations, or neither accepts it. -/
theorem exec_mirrors (storesFresh : body.StoresFresh U) :
    ∀ (events : List (Event Input)) {trailed direct : Config inventory Value},
      Mirrors body U trailed direct →
      Option.Rel (fun left right => left.1 = right.1 ∧ Mirrors body U left.2 right.2)
        (exec body .trailed trailed events) (exec body (.storeTrailed U) direct events)
  | [], _, _, mirrors => .some ⟨rfl, mirrors⟩
  | event :: events, trailed, direct, mirrors => by
      rw [exec_cons, exec_cons]
      refine rel_bind (next_mirrors storesFresh mirrors event) ?_
      intro left right same
      refine rel_map (exec_mirrors storesFresh events same.2) ?_
      intro leftResult rightResult sameResult
      exact ⟨by rw [same.1, sameResult.1], sameResult.2⟩

/-- At the entry the disciplines are mirrored when the activation leaves the
slots of `U` unassigned. -/
theorem entry_mirrors (slots : DenseEnvironment inventory Value)
    (unassigned : ∀ i ∈ U, slots i = none) :
    Mirrors body U (entry slots) (entry slots) :=
  ⟨rfl, rfl, .base rfl (fun _ member => by cases member)
    fun i inU _ => unassigned i inU⟩

/-- **Observational equivalence.**  When the activation leaves the slots of `U`
unassigned and the body writes a slot of `U` only where its path has not
stored it, the tier's discipline, which writes those slots in place and puts
the writes made while a choice point is live on the store trail, accepts the
same event lists as the discipline that trails every write, and shows the same
observations on them. -/
theorem exec_observations_eq (storesFresh : body.StoresFresh U)
    (slots : DenseEnvironment inventory Value) (unassigned : ∀ i ∈ U, slots i = none)
    (events : List (Event Input)) :
    (exec body .trailed (entry slots) events).map Prod.fst =
      (exec body (.storeTrailed U) (entry slots) events).map Prod.fst :=
  map_eq_of_rel (exec_mirrors storesFresh events (entry_mirrors slots unassigned))
    fun _ _ same => same.1

/-- **The same slot vector.**  Wherever both disciplines are after the same
events, they are at the same position and hold the same slots: any reader of
the whole vector, a collector included, sees in the tier's discipline what it
sees in the reference. -/
theorem exec_slots_eq (storesFresh : body.StoresFresh U)
    (slots : DenseEnvironment inventory Value) (unassigned : ∀ i ∈ U, slots i = none)
    (events : List (Event Input))
    {shownTrailed shownDirect : List (Obs inventory Value)}
    {trailed direct : Config inventory Value}
    (ranTrailed : exec body .trailed (entry slots) events = some (shownTrailed, trailed))
    (ranDirect : exec body (.storeTrailed U) (entry slots) events =
      some (shownDirect, direct)) :
    shownTrailed = shownDirect ∧ trailed.pos = direct.pos ∧
      trailed.state.slots = direct.state.slots := by
  have related := exec_mirrors storesFresh events (entry_mirrors slots unassigned)
  rw [ranTrailed, ranDirect] at related
  cases related with
  | some same =>
      obtain ⟨sameShown, samePos, _, mirror⟩ := same
      exact ⟨sameShown, samePos, mirror.same'⟩

/-- **No stale slot.**  In every configuration the tier's discipline reaches, a
slot of `U` the current path has not stored is empty. -/
theorem storeTrailed_unstored (storesFresh : body.StoresFresh U)
    (slots : DenseEnvironment inventory Value) (unassigned : ∀ i ∈ U, slots i = none)
    (events : List (Event Input)) {shown : List (Obs inventory Value)}
    {config : Config inventory Value}
    (ran : exec body (.storeTrailed U) (entry slots) events = some (shown, config)) :
    ∀ i ∈ U, i ∉ body.defined U config.pos → config.state.slots i = none := by
  have related := exec_mirrors storesFresh events (entry_mirrors slots unassigned)
  rw [ran] at related
  obtain ⟨⟨shownTrailed, trailed⟩, _, _, samePos, _, mirror⟩ := rel_some_inv_right related
  change trailed.pos = config.pos at samePos
  intro i inU notStored
  rw [← mirror.same']
  exact mirror.unstored' i inU (samePos ▸ notStored)

/-- **Collector safety.**  In every configuration the tier's discipline reaches,
every non-empty slot of `U` holds the value written by the most recent visit of
its store, which lies on the current path above the position where the
activation resumes: the observations contain that visit and no later visit of
its position. -/
theorem storeTrailed_collector_safe (storesFresh : body.StoresFresh U)
    (slots : DenseEnvironment inventory Value) (unassigned : ∀ i ∈ U, slots i = none)
    (events : List (Event Input)) {shown : List (Obs inventory Value)}
    {config : Config inventory Value}
    (ran : exec body (.storeTrailed U) (entry slots) events = some (shown, config)) :
    ∀ i ∈ U, ∀ value, config.state.slots i = some value →
      ∃ pre above seen wrote post,
        shown = pre ++ Obs.visit above seen wrote :: post ∧
        (∃ outcome, above ++ [outcome] <+: config.pos) ∧ body.WritesAt above i ∧
        (∀ later ∈ post, later.visited ≠ some above) ∧ wrote i = some value := by
  intro i inU value holds
  have stored : i ∈ body.defined U config.pos := by
    by_contra notStored
    rw [storeTrailed_unstored storesFresh slots unassigned events ran i inU notStored]
      at holds
    cases holds
  obtain ⟨_, _, recent⟩ := inPlace_most_recent_store storesFresh slots
    (discipline := .storeTrailed U) rfl events ran
  obtain ⟨pre, above, seen, wrote, post, shownEq, below, writes, noLater, value',
    wroteValue, holds'⟩ := recent i inU stored
  rw [holds] at holds'
  cases holds'
  exact ⟨pre, above, seen, wrote, post, shownEq, below, writes, noLater, wroteValue⟩

/-- A collector that traces every non-empty slot stays within the bound of
`restricted_reader_agrees`: every such slot is outside `U` or stored on the
current path. -/
theorem storeTrailed_nonempty_restricted (storesFresh : body.StoresFresh U)
    (slots : DenseEnvironment inventory Value) (unassigned : ∀ i ∈ U, slots i = none)
    (events : List (Event Input)) {shown : List (Obs inventory Value)}
    {config : Config inventory Value}
    (ran : exec body (.storeTrailed U) (entry slots) events = some (shown, config)) :
    ∀ i, (config.state.slots i).isSome → i ∉ U ∨ i ∈ body.defined U config.pos := by
  intro i nonEmpty
  by_cases inU : i ∈ U
  · by_contra neither
    rw [not_or, not_not] at neither
    rw [storeTrailed_unstored storesFresh slots unassigned events ran i inU neither.2]
      at nonEmpty
    cases nonEmpty
  · exact .inl inU

end StoreTrail

/-! ## Positive and negative witnesses -/

namespace Canary

/-- Two slots: `stored`, stored at its first occurrence, and `answer`, which a
choice point fills. -/
def slotNames : Inventory Nat := ⟨[0, 1], by decide⟩

def stored : slotNames.Slot := ⟨0, by decide⟩
def answer : slotNames.Slot := ⟨1, by decide⟩

/-- A choice point whose alternatives deliver their input as the answer. -/
def call : Step slotNames Nat Nat where
  reads := ∅
  writes := [answer]
  choice := true
  run _ input := some (fun _ => input, true)
  run_congr _ _ _ _ := rfl

/-- Store the answer's successor. -/
def storeSucc : Step slotNames Nat Nat where
  reads := {answer}
  writes := [stored]
  choice := false
  run slots _ := (slots answer).map fun value => (fun _ => value + 1, true)
  run_congr slots slots' _ agree := by rw [agree answer (Finset.mem_singleton_self _)]

/-- Read the stored slot and branch on its parity. -/
def readStored : Step slotNames Nat Nat where
  reads := {stored}
  writes := []
  choice := false
  run slots _ := (slots stored).map fun value => (fun _ => 0, value % 2 == 0)
  run_congr slots slots' _ agree := by rw [agree stored (Finset.mem_singleton_self _)]

/-- Call, store, read: `stored` is first stored on its only path. -/
def storedAfterCall : Body slotNames Nat Nat :=
  .node call fun _ => .node storeSucc fun _ => .node readStored fun _ => .stop

theorem storedAfterCall_firstStores : storedAfterCall.FirstStores {stored} :=
  Body.firstStores?_sound _ _ (by decide)

/-- The slot a list of observations' last visit saw. -/
def lastSeen (i : slotNames.Slot) (shown : List (Obs slotNames Nat)) :
    Option (Option Nat) :=
  match shown.getLast? with
  | some (.visit _ seen _) => some (seen i)
  | _ => none

/-- Answer 5, store 6, read it; backtrack into the call, answer 7, store 8,
read it.  The call leaves alternatives each time. -/
def storedAfterCallEvents : List (Event Nat) :=
  [.step 5 true, .step 0 true, .step 0 true, .back, .step 7 true, .step 0 true,
    .step 0 true]

/-- Right after the backtrack into the call, the untrailed discipline still
holds the 6 stored on the abandoned run, at the root, where the path has stored
nothing; the trailed and the store-trailed discipline hold nothing there.  The
reads see the same values in all three disciplines: the second read sees 8. -/
theorem storedAfterCall_disciplines :
    ((exec storedAfterCall (.untrailed {stored}) (entry fun _ => none)
        (storedAfterCallEvents.take 4)).map
        fun result => (result.2.pos, result.2.state.slots stored)) = some ([], some 6) ∧
      ((exec storedAfterCall .trailed (entry fun _ => none)
        (storedAfterCallEvents.take 4)).map
        fun result => result.2.state.slots stored) = some none ∧
      ((exec storedAfterCall (.storeTrailed {stored}) (entry fun _ => none)
        (storedAfterCallEvents.take 4)).map
        fun result => result.2.state.slots stored) = some none ∧
      ((exec storedAfterCall .trailed (entry fun _ => none) storedAfterCallEvents).map
        fun result => lastSeen stored result.1) = some (some (some 8)) ∧
      (exec storedAfterCall .trailed (entry fun _ => none) storedAfterCallEvents).map
          Prod.fst =
        (exec storedAfterCall (.untrailed {stored}) (entry fun _ => none)
          storedAfterCallEvents).map Prod.fst ∧
      (exec storedAfterCall .trailed (entry fun _ => none) storedAfterCallEvents).map
          Prod.fst =
        (exec storedAfterCall (.storeTrailed {stored}) (entry fun _ => none)
          storedAfterCallEvents).map Prod.fst :=
  ⟨by decide, by decide, by decide, by decide,
    exec_observations_eq_untrailed storedAfterCall_firstStores _ _,
    exec_observations_eq storedAfterCall_firstStores.storesFresh _ (fun _ _ => rfl) _⟩

/-- **Negative witness: without the store trail a slot goes stale.**  The
untrailed discipline reaches a configuration with a non-empty slot of `U` that
the current path has not stored, so a collector tracing every non-empty slot
reads a value the current path never stored.  The store-trailed discipline
never does (`storeTrailed_collector_safe`). -/
theorem untrailed_keeps_stale_slot :
    ∃ (events : List (Event Nat)) (shown : List (Obs slotNames Nat))
      (config : Config slotNames Nat),
      exec storedAfterCall (.untrailed {stored}) (entry fun _ => none) events =
        some (shown, config) ∧
      config.state.slots stored = some 6 ∧
      stored ∉ storedAfterCall.defined {stored} config.pos := by
  obtain ⟨⟨shown, config⟩, runs, same⟩ :=
    Option.map_eq_some_iff.mp storedAfterCall_disciplines.1
  simp only [Prod.mk.injEq] at same
  exact ⟨_, shown, config, runs, same.2, by rw [same.1]; decide⟩

/-- A choice point branching on its input: `0` selects the first branch. -/
def choose : Step slotNames Nat Nat where
  reads := ∅
  writes := []
  choice := true
  run _ input := some (fun _ => 0, input == 0)
  run_congr _ _ _ _ := rfl

/-- Store 7. -/
def storeSeven : Step slotNames Nat Nat where
  reads := ∅
  writes := [stored]
  choice := false
  run _ _ := some (fun _ => 7, true)
  run_congr _ _ _ _ := rfl

/-- Read the stored slot, branching on whether it holds a value. -/
def readRaw : Step slotNames Nat Nat where
  reads := {stored}
  writes := []
  choice := false
  run slots _ := some (fun _ => 0, (slots stored).isSome)
  run_congr slots slots' _ agree := by rw [agree stored (Finset.mem_singleton_self _)]

/-- One branch stores `stored`, the other reads it without storing it. -/
def readBeforeStore : Body slotNames Nat Nat :=
  .node choose fun first =>
    if first then .node storeSeven fun _ => .stop
    else .node readRaw fun _ => .stop

/-- The read on the second branch violates the first-occurrence condition. -/
theorem readBeforeStore_not_firstStores : ¬ readBeforeStore.FirstStores {stored} := by
  intro firstStores
  have readDefined := (firstStores [false] readRaw _ rfl).1
    (Finset.mem_inter.mpr ⟨Finset.mem_singleton_self stored, Finset.mem_singleton_self stored⟩)
  revert readDefined
  decide

/-- Its writes still meet the write half. -/
theorem readBeforeStore_storesFresh : readBeforeStore.StoresFresh {stored} :=
  Body.storesFresh?_sound _ _ (by decide)

/-- Take the storing branch, backtrack, take the reading branch, read. -/
def counterTrace : List (Event Nat) :=
  [.step 0 true, .step 0 true, .back, .step 1 true, .step 0 true]

/-- **Negative counter-trace.**  After the backtrack the trailed discipline has
unassigned `stored` again, the untrailed one still holds 7, and the read on the
other branch sees different values: without the read half of the condition the
untrailed in-place write is observable.  The store-trailed discipline empties
the slot at the backtrack and sees what the trailed one sees. -/
theorem readBeforeStore_counterTrace :
    ((exec readBeforeStore .trailed (entry fun _ => none) counterTrace).map
        fun result => lastSeen stored result.1) = some (some none) ∧
      ((exec readBeforeStore (.untrailed {stored}) (entry fun _ => none) counterTrace).map
        fun result => lastSeen stored result.1) = some (some (some 7)) ∧
      ((exec readBeforeStore (.storeTrailed {stored}) (entry fun _ => none)
        counterTrace).map fun result => lastSeen stored result.1) = some (some none) := by
  decide

theorem readBeforeStore_observable :
    (exec readBeforeStore .trailed (entry fun _ => none) counterTrace).map Prod.fst ≠
      (exec readBeforeStore (.untrailed {stored}) (entry fun _ => none) counterTrace).map
        Prod.fst := by
  intro same
  have seen := congrArg (Option.map (lastSeen stored)) same
  rw [Option.map_map, Option.map_map] at seen
  have composed : (lastSeen stored ∘ Prod.fst :
      List (Obs slotNames Nat) × Config slotNames Nat → Option (Option Nat)) =
      fun result => lastSeen stored result.1 := rfl
  rw [composed, readBeforeStore_counterTrace.1, readBeforeStore_counterTrace.2.1] at seen
  simp at seen

/-- The store trail repairs it: the body meets the write half, so the
store-trailed discipline shows exactly the trailed observations. -/
theorem readBeforeStore_storeTrailed_equal :
    (exec readBeforeStore .trailed (entry fun _ => none) counterTrace).map Prod.fst =
      (exec readBeforeStore (.storeTrailed {stored}) (entry fun _ => none)
        counterTrace).map Prod.fst :=
  exec_observations_eq readBeforeStore_storesFresh _ (fun _ _ => rfl) _

/-- The classification pass writes `stored` in place in the call-store-read
body, and refuses to on the body whose other branch reads it first. -/
theorem classification_witnesses :
    stored ∈ Body.firstStoreSlots ∅ storedAfterCall ∧
      stored ∉ Body.firstStoreSlots ∅ readBeforeStore := by
  decide

end Canary

end Mettapedia.GSLT.LanguageDef.FirstOccurrenceStores
