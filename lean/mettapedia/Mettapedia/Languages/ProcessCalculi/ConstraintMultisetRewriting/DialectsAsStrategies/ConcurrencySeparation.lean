import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.LanguageOnTheStep

/-!
# Match then remove is not a take: the concurrency separation

A **take** of the step consumes its footprint in one firing. A PeTTa or HE program without a native
take writes it as a `match` followed by `remove-atom`s and `add-atom`s, each a single-atom operation
on the shared store. This module says exactly when the two agree.

## The model

* The store is a bag of ground atoms (`Multiset α`). A **take** (`Take`) lists what it takes,
  reads and makes; it is admitted when its takes and reads are present as distinct copies, and its
  firing removes the takes and adds the makes (`Take.fire`, `Take.block`).
* Single-atom operations (`Op`): a `query` of a conjunction at one instant (a match, read as a
  snapshot of the whole conjunction, the most favourable reading for the encoding), `remove`,
  `add`. The **encoding** of a take (`Take.encode`) is the query of its takes and reads, then the
  removals, then the additions.
* **Removal** (`Removal`) as the engines do it, checked in their sources: SWI-PeTTa and CeTTa's
  PeTTa lane remove every copy and answer whether one was there (`all := true`); HE and CeTTa's HE
  lane remove one copy and answer unit either way (`all := false`). A program that tests the answer
  ends its branch when nothing was removed (`checked := true`); one that ignores it goes on.
* **Interleaving** (`Interleave`): threads, as hyperpose runs them, take turns one operation at a
  time on one store; a thread whose operation fails ends with no answer. **Serial** runs
  (`Serial`) run whole blocks, one thread at a time, for any block semantics.

## Results

* **Sequential exactness** (`sequential_exact`): run without interruption, the encoding of a take
  whose takes and reads are distinct atoms is the take: same store, same answer. With removal of
  every copy this needs each taken atom to be single in the store.
* **A global lock around each deterministic body restores exactly the serial atomic runs.** A body
  here is one sequence of single-atom operations, so it answers at most once. `LockedStep` is the
  interleaving with one lock around each whole body: a thread takes the lock with its first
  operation and keeps it until it finishes or dies, and no other thread is scheduled meanwhile.
  `lock_exact`: its outcomes are exactly those of the bodies run one after another in every order.
  `lock_restores_serial`: for takes of distinct atoms with removal of one copy, those are exactly
  the outcomes of the atomic takes. `global_lock_exact` joins the two. On such bodies a lock that
  keeps every branch and a lock committed to the first answer coincide. SWI's `with_mutex/2` and
  `transaction/1` are committed: they run their goal as `once/1`, so around a nondeterministic
  producer they keep one answer (`PeTTaHE.onceLocked`, `PeTTaHE.Controls.once_lock_loses_answers`).
  PeTTa also removes every copy, outside `global_lock_exact`'s hypothesis.
* **Serial runs are interleavings** (`serial_sub_interleaved`): for takes of distinct atoms with
  removal of one copy, every outcome of the serial atomic runs is an outcome of the interleaved
  encodings.
* **The race** (`race`): for every removal policy, two threads encoding takes of the same two
  atoms reach an outcome under interleaving that no sequence of atomic firings produces: with
  checked removals both threads die and both atoms are lost; with unchecked removals both threads
  answer and both outputs are made.
* **Atomic firings run in parallel** (`atomic_parallel`): on the step itself, two check-free
  firings whose footprints do not interfere run in either order to the same configuration up to
  solutions (`linearTake_interchange`); on bags, two jointly admitted takes commute
  (`Take.fire_comm`). Every interleaving of atomic firings is a run of the step, so atomicity
  leaves no race to explain, only choices.

In CALM's terms (Hellerstein; Ameloot, Neven and Van den Bussche): a match establishes presence
*in this snapshot*; a take needs presence *throughout the region* up to its removal. The race is a
snapshot that does not protect its region; the lock and the atomic firing are the two ways to
protect it.

* **Absence in a snapshot races too** (`snapshot_absence_races`): two threads that never remove,
  each adding an atom and then matching the other's, both answer under interleaving, while run one
  after the other at most one answers. A match that comes back empty observes absence in its
  snapshot, so in PeTTa even reading and adding needs coordination. The step's rules that read and
  make, whose reads wait for their atoms, need none: they reach the same facts in every order
  (`MonotoneInference.confluent`, used in `LanguageOnTheStep`). That is sufficiency; no theorem here
  says this fragment is exactly the coordination-free one.

## Controls

* `Controls.repeated_atom_inexact`: a take of two copies of one atom, encoded, is not the take even
  sequentially: a match does not count copies.
* `Controls.remove_all_loses_copy`: with removal of every copy, the encoding of a take of one copy
  from a store holding two loses the second; with removal of one copy it is exact.
* `Controls.conflict_is_choice`: two atomic takers of one atom are each admitted, not both: the
  serial outcomes are two, and each is a legitimate one.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies

namespace Concurrency

variable {α : Type*} [DecidableEq α] {β : Type*}

/-! ## Takes on a bag of atoms -/

/-- **A take**: what it takes, reads and makes. -/
structure Take (α : Type*) where
  take : List α
  read : List α
  make : List α

namespace Take

/-- Admitted when the takes and reads are present as distinct copies. -/
def Admits (f : Take α) (s : Multiset α) : Prop := ((f.take ++ f.read : List α) : Multiset α) ≤ s

instance (f : Take α) (s : Multiset α) : Decidable (f.Admits s) :=
  inferInstanceAs (Decidable (_ ≤ _))

/-- The firing: remove the takes, add the makes. -/
def fire (f : Take α) (s : Multiset α) : Multiset α := s - (f.take : Multiset α) + f.make

/-- The take as one block: the new store, and whether it fired. -/
def block (f : Take α) (s : Multiset α) : Multiset α × Bool :=
  if f.Admits s then (f.fire s, true) else (s, false)

omit [DecidableEq α] in
theorem take_le {f : Take α} {s : Multiset α} (admitted : f.Admits s) : (f.take : Multiset α) ≤ s :=
  le_trans (by rw [← Multiset.coe_add]; exact le_add_right le_rfl) admitted

/-- **Jointly admitted takes commute**: each stays admitted after the other, and the two orders
end in the same store. -/
theorem fire_comm (f g : Take α) (s : Multiset α)
    (joint : ((f.take ++ f.read : List α) : Multiset α) + ((g.take ++ g.read : List α) : Multiset α) ≤ s) :
    g.Admits (f.fire s) ∧ f.Admits (g.fire s) ∧ g.fire (f.fire s) = f.fire (g.fire s) := by
  have fTake : (f.take : Multiset α) ≤ ((f.take ++ f.read : List α) : Multiset α) := by
    rw [← Multiset.coe_add]; exact Multiset.le_add_right _ _
  have gTake : (g.take : Multiset α) ≤ ((g.take ++ g.read : List α) : Multiset α) := by
    rw [← Multiset.coe_add]; exact Multiset.le_add_right _ _
  have gAfter : ((g.take ++ g.read : List α) : Multiset α) ≤ s - (f.take : Multiset α) :=
    le_tsub_of_add_le_left (le_trans (add_le_add fTake le_rfl) joint)
  have fAfter : ((f.take ++ f.read : List α) : Multiset α) ≤ s - (g.take : Multiset α) :=
    le_tsub_of_add_le_left (le_trans (add_le_add gTake le_rfl) (by rw [add_comm]; exact joint))
  have gIn : (g.take : Multiset α) ≤ s - (f.take : Multiset α) := le_trans gTake gAfter
  have fIn : (f.take : Multiset α) ≤ s - (g.take : Multiset α) := le_trans fTake fAfter
  refine ⟨le_trans gAfter (Multiset.le_add_right _ _), le_trans fAfter (Multiset.le_add_right _ _), ?_⟩
  unfold fire
  rw [← tsub_add_eq_add_tsub gIn, ← tsub_add_eq_add_tsub fIn, tsub_tsub, tsub_tsub,
    add_comm (f.take : Multiset α) (g.take : Multiset α), add_assoc, add_assoc,
    add_comm (f.make : Multiset α)]

end Take

/-! ## Single-atom operations -/

/-- **Removal** as an engine does it. -/
structure Removal where
  /-- Every copy is removed (SWI-PeTTa, CeTTa's PeTTa lane), not one (HE, CeTTa's HE lane). -/
  all : Bool
  /-- A removal that finds nothing ends the branch (the program tests the answer). -/
  checked : Bool

/-- One removal: `none` ends the branch. -/
def Removal.apply (pol : Removal) (a : α) (s : Multiset α) : Option (Multiset α) :=
  if a ∈ s then some (if pol.all then s.filter (· ≠ a) else s.erase a)
  else if pol.checked then none else some s

/-- **Single-atom operations**. -/
inductive Op (α : Type*)
  /-- A match of a conjunction, at one instant. -/
  | query (atoms : List α)
  | remove (a : α)
  | add (a : α)

/-- One operation: `none` ends the branch. -/
def Op.run (pol : Removal) : Op α → Multiset α → Option (Multiset α)
  | .query atoms, s => if ∀ a ∈ atoms, a ∈ s then some s else none
  | .remove a, s => pol.apply a s
  | .add a, s => some (a ::ₘ s)

/-- **The encoding of a take**: query its takes and reads, remove its takes, add its makes. -/
def Take.encode (f : Take α) : List (Op α) :=
  .query (f.take ++ f.read) :: (f.take.map .remove ++ f.make.map .add)

/-- Running operations without interruption: the store reached, and whether the branch got through. -/
def runOps (pol : Removal) : List (Op α) → Multiset α → Multiset α × Bool
  | [], s => (s, true)
  | o :: rest, s =>
      match o.run pol s with
      | some s' => runOps pol rest s'
      | none => (s, false)

theorem runOps_cons_some {pol : Removal} {o : Op α} {rest : List (Op α)} {s s' : Multiset α}
    (h : o.run pol s = some s') : runOps pol (o :: rest) s = runOps pol rest s' := by
  simp only [runOps, h]

theorem runOps_cons_none {pol : Removal} {o : Op α} {rest : List (Op α)} {s : Multiset α}
    (h : o.run pol s = none) : runOps pol (o :: rest) s = (s, false) := by
  simp only [runOps, h]

theorem filter_ne_eq_erase {a : α} {s : Multiset α} (single : s.count a ≤ 1) :
    s.filter (· ≠ a) = s.erase a := by
  ext b
  by_cases same : b = a
  · rw [same, Multiset.count_filter_of_neg (p := fun x => x ≠ a) (fun h => h rfl),
      Multiset.count_erase_self]
    omega
  · rw [Multiset.count_filter_of_pos (p := fun x => x ≠ a) same, Multiset.count_erase_of_ne same]

theorem run_remove_present (pol : Removal) {a : α} {s : Multiset α} (present : a ∈ s)
    (single : pol.all = true → s.count a ≤ 1) : (Op.remove a).run pol s = some (s.erase a) := by
  simp only [Op.run, Removal.apply, if_pos present]
  cases h : pol.all
  · rfl
  · rw [if_pos rfl, filter_ne_eq_erase (single h)]

theorem run_remove_absent (pol : Removal) {a : α} {s : Multiset α} (absent : a ∉ s) :
    (Op.remove a).run pol s = if pol.checked then none else some s := by
  simp only [Op.run, Removal.apply, if_neg absent]

theorem run_query_pass (pol : Removal) {l : List α} {s : Multiset α} (present : ∀ a ∈ l, a ∈ s) :
    (Op.query l).run pol s = some s := by
  simp only [Op.run, if_pos present]

theorem runOps_adds (pol : Removal) : ∀ (l : List α) (s : Multiset α),
    runOps pol (l.map Op.add) s = (s + l, true)
  | [], s => by simp [runOps]
  | a :: l, s => by
      rw [List.map_cons, runOps_cons_some (show (Op.add a).run pol s = some (a ::ₘ s) from rfl),
        runOps_adds pol l (a ::ₘ s), ← Multiset.cons_coe, Multiset.add_cons, Multiset.cons_add]

theorem runOps_removes (pol : Removal) (rest : List (Op α)) : ∀ (l : List α) (s : Multiset α),
    l.Nodup → (∀ a ∈ l, a ∈ s) → (pol.all = true → ∀ a ∈ l, s.count a ≤ 1) →
      runOps pol (l.map Op.remove ++ rest) s = runOps pol rest (s - l)
  | [], s, _, _, _ => by simp
  | a :: l, s, distinct, present, single => by
      obtain ⟨notIn, distinct'⟩ := List.nodup_cons.mp distinct
      have here : a ∈ s := present a List.mem_cons_self
      rw [List.map_cons, List.cons_append,
        runOps_cons_some (run_remove_present pol here (fun all => single all a List.mem_cons_self)),
        runOps_removes pol rest l (s.erase a) distinct' ?_ ?_, ← Multiset.cons_coe, Multiset.sub_cons]
      · intro b member
        have ne : b ≠ a := fun same => notIn (same ▸ member)
        exact (Multiset.mem_erase_of_ne ne).mpr (present b (List.mem_cons_of_mem a member))
      · intro all b member
        have ne : b ≠ a := fun same => notIn (same ▸ member)
        rw [Multiset.count_erase_of_ne ne]
        exact single all b (List.mem_cons_of_mem a member)

/-- **Sequential exactness**: run without interruption, the encoding of a take whose takes and
reads are distinct atoms is the take. With removal of every copy, each taken atom must be single
in the store. -/
theorem sequential_exact (pol : Removal) (f : Take α) (s : Multiset α)
    (linear : (f.take ++ f.read).Nodup) (single : pol.all = true → ∀ a ∈ f.take, s.count a ≤ 1) :
    runOps pol f.encode s = f.block s := by
  by_cases admitted : f.Admits s
  · have present : ∀ a ∈ f.take ++ f.read, a ∈ s :=
      fun a member => Multiset.mem_of_le admitted (Multiset.mem_coe.mpr member)
    have takePresent : ∀ a ∈ f.take, a ∈ s := fun a member => present a (List.mem_append_left _ member)
    rw [Take.encode, runOps_cons_some (run_query_pass pol present),
      runOps_removes pol _ f.take s (List.Nodup.sublist (List.sublist_append_left _ _) linear)
        takePresent single, runOps_adds, Take.block, if_pos admitted, Take.fire]
  · have fails : (Op.query (f.take ++ f.read)).run pol s = none := by
      show (if ∀ a ∈ f.take ++ f.read, a ∈ s then some s else none) = none
      rw [if_neg]
      intro present
      exact admitted ((Multiset.le_iff_subset (Multiset.coe_nodup.mpr linear)).mpr
        (fun a member => present a (Multiset.mem_coe.mp member)))
    rw [Take.encode, runOps_cons_none fails, Take.block, if_neg admitted]

/-! ## Interleaved and serial runs -/

/-- A configuration of interleaved threads: the store, the running threads with their remaining
operations and answers, and the answers given so far. -/
structure Config (α β : Type*) where
  store : Multiset α
  threads : List (List (Op α) × β)
  answers : Multiset β

/-- **Interleaving**: any thread may move next, one operation at a time. -/
inductive Interleave (pol : Removal) : Config α β → Config α β → Prop
  | shuffle {s : Multiset α} {ts ts' : List (List (Op α) × β)} {ans : Multiset β} :
      ts.Perm ts' → Interleave pol ⟨s, ts, ans⟩ ⟨s, ts', ans⟩
  | op {s s' : Multiset α} {o : Op α} {code : List (Op α)} {b : β} {ts : List (List (Op α) × β)}
      {ans : Multiset β} : o.run pol s = some s' →
      Interleave pol ⟨s, (o :: code, b) :: ts, ans⟩ ⟨s', (code, b) :: ts, ans⟩
  | die {s : Multiset α} {o : Op α} {code : List (Op α)} {b : β} {ts : List (List (Op α) × β)}
      {ans : Multiset β} : o.run pol s = none →
      Interleave pol ⟨s, (o :: code, b) :: ts, ans⟩ ⟨s, ts, ans⟩
  | finish {s : Multiset α} {b : β} {ts : List (List (Op α) × β)} {ans : Multiset β} :
      Interleave pol ⟨s, ([], b) :: ts, ans⟩ ⟨s, ts, b ::ₘ ans⟩

/-- The outcomes of interleaved threads: answer bag and final store, once every thread is done. -/
def interleavedOutcomes (pol : Removal) (s : Multiset α) (ts : List (List (Op α) × β)) :
    Set (Multiset β × Multiset α) :=
  {o | Relation.ReflTransGen (Interleave pol) ⟨s, ts, 0⟩ ⟨o.2, [], o.1⟩}

/-- A serial configuration: the store, the pending threads, the answers so far. -/
structure SConfig (α γ β : Type*) where
  store : Multiset α
  pending : List γ
  answers : Multiset β

/-- **Serial runs**: one whole block at a time, in any order. -/
inductive Serial {γ : Type*} (block : γ → Multiset α → Multiset α × Bool) (answer : γ → β) :
    SConfig α γ β → SConfig α γ β → Prop
  | shuffle {s : Multiset α} {ts ts' : List γ} {ans : Multiset β} :
      ts.Perm ts' → Serial block answer ⟨s, ts, ans⟩ ⟨s, ts', ans⟩
  | run {s : Multiset α} {t : γ} {ts : List γ} {ans : Multiset β} :
      Serial block answer ⟨s, t :: ts, ans⟩
        ⟨(block t s).1, ts, if (block t s).2 then answer t ::ₘ ans else ans⟩

/-- The outcomes of serial runs. -/
def serialOutcomes {γ : Type*} (block : γ → Multiset α → Multiset α × Bool) (answer : γ → β)
    (s : Multiset α) (ts : List γ) : Set (Multiset β × Multiset α) :=
  {o | Relation.ReflTransGen (Serial block answer) ⟨s, ts, 0⟩ ⟨o.2, [], o.1⟩}

/-- The atomic semantics: each take fires as one block. -/
abbrev atomic : Take α × β → Multiset α → Multiset α × Bool := fun t s => t.1.block s

/-- The locked semantics: each encoded body runs as one block. -/
abbrev locked (pol : Removal) : Take α × β → Multiset α → Multiset α × Bool :=
  fun t s => runOps pol t.1.encode s

omit [DecidableEq α] in
/-- A serial move whose block result is known. -/
theorem serial_run_eq {γ : Type*} {block : γ → Multiset α → Multiset α × Bool} {answer : γ → β}
    {s s' : Multiset α} {t : γ} {ts : List γ} {ans : Multiset β} {fired : Bool}
    (h : block t s = (s', fired)) :
    Serial block answer ⟨s, t :: ts, ans⟩ ⟨s', ts, if fired then answer t ::ₘ ans else ans⟩ := by
  have step := Serial.run (block := block) (answer := answer) (s := s) (t := t) (ts := ts) (ans := ans)
  rw [h] at step
  exact step

omit [DecidableEq α] in
/-- Serial runs depend on the blocks of the threads they hold only. -/
theorem serial_congr {γ : Type*} {block₁ block₂ : γ → Multiset α → Multiset α × Bool}
    {answer : γ → β} (ts₀ : List γ) (agree : ∀ t ∈ ts₀, block₁ t = block₂ t)
    {x y : SConfig α γ β} (path : Relation.ReflTransGen (Serial block₁ answer) x y) :
    (∀ t ∈ x.pending, t ∈ ts₀) → Relation.ReflTransGen (Serial block₂ answer) x y := by
  induction path using Relation.ReflTransGen.head_induction_on with
  | refl => exact fun _ => .refl
  | head step _ later =>
      intro inside
      cases step with
      | shuffle perm =>
          exact .head (.shuffle perm) (later fun t member => inside t (perm.symm.subset member))
      | @run s t ts ans =>
          have same := agree t (inside t List.mem_cons_self)
          have next := later fun u member => inside u (List.mem_cons_of_mem t member)
          rw [same] at next
          exact .head .run next

/-- **A global lock restores exactly the serial atomic runs**, for removal of one copy and takes of
distinct atoms. -/
theorem lock_restores_serial (pol : Removal) (one : pol.all = false) (s : Multiset α)
    (ts : List (Take α × β)) (linear : ∀ t ∈ ts, (t.1.take ++ t.1.read).Nodup) :
    serialOutcomes (locked pol) Prod.snd s ts = serialOutcomes atomic Prod.snd s ts := by
  have agree : ∀ t ∈ ts, locked pol t = atomic t := fun t member => by
    funext s
    exact sequential_exact pol t.1 s (linear t member) (fun all => absurd (one.symm.trans all) (by decide))
  ext o
  exact ⟨fun path => serial_congr ts agree path (fun _ member => member),
    fun path => serial_congr ts (fun t member => (agree t member).symm) path (fun _ member => member)⟩

/-- A whole body runs as a sequence of interleaving moves. -/
theorem interleave_block (pol : Removal) : ∀ (code : List (Op α)) (s : Multiset α) (b : β)
    (ts : List (List (Op α) × β)) (ans : Multiset β),
    Relation.ReflTransGen (Interleave pol) ⟨s, (code, b) :: ts, ans⟩
      ⟨(runOps pol code s).1, ts, if (runOps pol code s).2 then b ::ₘ ans else ans⟩
  | [], s, b, ts, ans => .single .finish
  | o :: code, s, b, ts, ans => by
      cases h : o.run pol s with
      | none =>
          rw [runOps_cons_none h]
          exact .single (.die h)
      | some s' =>
          rw [runOps_cons_some h]
          exact .head (.op h) (interleave_block pol code s' b ts ans)

/-- Serial configurations of encoded bodies, seen as interleaved ones. -/
def embed (x : SConfig α (Take α × β) β) : Config α β :=
  ⟨x.store, x.pending.map fun t => (t.1.encode, t.2), x.answers⟩

theorem locked_interleaved (pol : Removal) {x y : SConfig α (Take α × β) β}
    (path : Relation.ReflTransGen (Serial (locked pol) Prod.snd) x y) :
    Relation.ReflTransGen (Interleave pol) (embed x) (embed y) := by
  induction path with
  | refl => exact .refl
  | tail _ step earlier =>
      refine earlier.trans ?_
      cases step with
      | shuffle perm => exact .single (.shuffle (perm.map _))
      | @run s t ts ans => exact interleave_block pol t.1.encode s t.2 _ ans

/-- **Serial atomic runs are interleavings** of the encodings, for removal of one copy and takes of
distinct atoms. -/
theorem serial_sub_interleaved (pol : Removal) (one : pol.all = false) (s : Multiset α)
    (ts : List (Take α × β)) (linear : ∀ t ∈ ts, (t.1.take ++ t.1.read).Nodup) :
    serialOutcomes atomic Prod.snd s ts ⊆
      interleavedOutcomes pol s (ts.map fun t => (t.1.encode, t.2)) := by
  intro o member
  rw [← lock_restores_serial pol one s ts linear] at member
  exact locked_interleaved pol member

/-! ## A real lock: no preemption while a body runs -/

/-- An interleaved configuration with a lock, held by the first thread when `busy`. -/
structure LConfig (α β : Type*) where
  store : Multiset α
  threads : List (List (Op α) × β)
  answers : Multiset β
  busy : Bool

/-- **Interleaving under a global lock around each whole body**: a thread takes the lock with its
first operation and keeps it until it finishes or dies; while the lock is held, no other thread is
scheduled. Each body is one sequence of operations and answers at most once, so this lock and one
committed to the body's first answer (SWI's `with_mutex/2`, which runs its goal as `once/1`)
coincide here; around a nondeterministic producer they differ (`PeTTaHE.onceLocked`). -/
inductive LockedStep (pol : Removal) : LConfig α β → LConfig α β → Prop
  | shuffle {s : Multiset α} {ts ts' : List (List (Op α) × β)} {ans : Multiset β} :
      ts.Perm ts' → LockedStep pol ⟨s, ts, ans, false⟩ ⟨s, ts', ans, false⟩
  | op {s s' : Multiset α} {o : Op α} {code : List (Op α)} {b : β} {ts : List (List (Op α) × β)}
      {ans : Multiset β} {busy : Bool} : o.run pol s = some s' →
      LockedStep pol ⟨s, (o :: code, b) :: ts, ans, busy⟩ ⟨s', (code, b) :: ts, ans, true⟩
  | die {s : Multiset α} {o : Op α} {code : List (Op α)} {b : β} {ts : List (List (Op α) × β)}
      {ans : Multiset β} {busy : Bool} : o.run pol s = none →
      LockedStep pol ⟨s, (o :: code, b) :: ts, ans, busy⟩ ⟨s, ts, ans, false⟩
  | finish {s : Multiset α} {b : β} {ts : List (List (Op α) × β)} {ans : Multiset β} {busy : Bool} :
      LockedStep pol ⟨s, ([], b) :: ts, ans, busy⟩ ⟨s, ts, b ::ₘ ans, false⟩

/-- The outcomes under the lock. -/
def lockedOutcomes (pol : Removal) (s : Multiset α) (ts : List (List (Op α) × β)) :
    Set (Multiset β × Multiset α) :=
  {o | Relation.ReflTransGen (LockedStep pol) ⟨s, ts, 0, false⟩ ⟨o.2, [], o.1, false⟩}

/-- Bodies as blocks. -/
abbrev bodies (pol : Removal) : List (Op α) × β → Multiset α → Multiset α × Bool :=
  fun t s => runOps pol t.1 s

/-- A locked configuration read serially: a body under way is completed. -/
def complete (pol : Removal) : LConfig α β → SConfig α (List (Op α) × β) β
  | ⟨s, (code, b) :: ts, ans, true⟩ =>
      ⟨(runOps pol code s).1, ts, if (runOps pol code s).2 then b ::ₘ ans else ans⟩
  | ⟨s, ts, ans, _⟩ => ⟨s, ts, ans⟩

theorem complete_free (pol : Removal) (s : Multiset α) (ts : List (List (Op α) × β)) (ans : Multiset β) :
    complete pol ⟨s, ts, ans, false⟩ = ⟨s, ts, ans⟩ := by
  cases ts <;> rfl

theorem complete_busy (pol : Removal) (s : Multiset α) (code : List (Op α)) (b : β)
    (ts : List (List (Op α) × β)) (ans : Multiset β) :
    complete pol ⟨s, (code, b) :: ts, ans, true⟩ =
      ⟨(runOps pol code s).1, ts, if (runOps pol code s).2 then b ::ₘ ans else ans⟩ := rfl

/-- **A locked step is at most one serial step** of the completed configurations. -/
theorem locked_simulates (pol : Removal) {x y : LConfig α β} (step : LockedStep pol x y) :
    Relation.ReflTransGen (Serial (bodies pol) Prod.snd) (complete pol x) (complete pol y) := by
  cases step with
  | shuffle perm =>
      rw [complete_free, complete_free]
      exact .single (.shuffle perm)
  | @op s s' o code b ts ans busy ran =>
      cases busy
      · rw [complete_free]
        have block := serial_run_eq (block := bodies pol) (answer := Prod.snd) (ts := ts) (ans := ans)
          (t := (o :: code, b)) (s := s) (runOps_cons_some (rest := code) ran)
        exact .single block
      · have same : complete pol ⟨s, (o :: code, b) :: ts, ans, true⟩ =
            complete pol ⟨s', (code, b) :: ts, ans, true⟩ := by
          rw [complete_busy, complete_busy, runOps_cons_some ran]
        exact (congrArg (fun z => Relation.ReflTransGen (Serial (bodies pol) Prod.snd) z
          (complete pol ⟨s', (code, b) :: ts, ans, true⟩)) same).mpr .refl
  | @die s o code b ts ans busy dead =>
      cases busy
      · rw [complete_free, complete_free]
        have block := serial_run_eq (block := bodies pol) (answer := Prod.snd) (ts := ts) (ans := ans)
          (t := (o :: code, b)) (s := s) (runOps_cons_none (rest := code) dead)
        exact .single block
      · have same : complete pol ⟨s, (o :: code, b) :: ts, ans, true⟩ = complete pol ⟨s, ts, ans, false⟩ := by
          simp [complete_busy, complete_free, runOps_cons_none dead]
        exact (congrArg (fun z => Relation.ReflTransGen (Serial (bodies pol) Prod.snd) z
          (complete pol ⟨s, ts, ans, false⟩)) same).mpr .refl
  | @finish s b ts ans busy =>
      cases busy
      · rw [complete_free, complete_free]
        exact .single (serial_run_eq (block := bodies pol) (answer := Prod.snd) (t := ([], b))
          (s := s) (ts := ts) (ans := ans) rfl)
      · rw [complete_free]
        exact .refl

/-- A whole body runs under the lock without preemption. -/
theorem locked_block (pol : Removal) : ∀ (code : List (Op α)) (s : Multiset α) (b : β)
    (ts : List (List (Op α) × β)) (ans : Multiset β) (busy : Bool),
    Relation.ReflTransGen (LockedStep pol) ⟨s, (code, b) :: ts, ans, busy⟩
      ⟨(runOps pol code s).1, ts, if (runOps pol code s).2 then b ::ₘ ans else ans, false⟩
  | [], s, b, ts, ans, busy => .single .finish
  | o :: code, s, b, ts, ans, busy => by
      cases h : o.run pol s with
      | none =>
          rw [runOps_cons_none h]
          exact .single (.die h)
      | some s' =>
          rw [runOps_cons_some h]
          exact .head (.op h) (locked_block pol code s' b ts ans true)

/-- **The lock gives exactly the serial runs of whole bodies**, for bodies that are single sequences
of operations, each answering at most once. -/
theorem lock_exact (pol : Removal) (s : Multiset α) (ts : List (List (Op α) × β)) :
    lockedOutcomes pol s ts = serialOutcomes (bodies pol) Prod.snd s ts := by
  ext o
  constructor
  · intro path
    have serial : ∀ {x y : LConfig α β}, Relation.ReflTransGen (LockedStep pol) x y →
        Relation.ReflTransGen (Serial (bodies pol) Prod.snd) (complete pol x) (complete pol y) := by
      intro x y path
      induction path with
      | refl => exact .refl
      | tail _ step earlier => exact earlier.trans (locked_simulates pol step)
    have := serial path
    rwa [complete_free, complete_free] at this
  · intro path
    have locked : ∀ {x y : SConfig α (List (Op α) × β) β},
        Relation.ReflTransGen (Serial (bodies pol) Prod.snd) x y →
        Relation.ReflTransGen (LockedStep pol) ⟨x.store, x.pending, x.answers, false⟩
          ⟨y.store, y.pending, y.answers, false⟩ := by
      intro x y path
      induction path with
      | refl => exact .refl
      | tail _ step earlier =>
          refine earlier.trans ?_
          cases step with
          | shuffle perm => exact .single (.shuffle perm)
          | @run s t ts ans => exact locked_block pol t.1 s t.2 ts ans false
    exact locked path

omit [DecidableEq α] in
/-- Reordering a mapped list reorders the list. -/
theorem perm_lift {γ δ : Type*} (f : γ → δ) : ∀ (l : List γ) (m : List δ),
    (l.map f).Perm m → ∃ l' : List γ, l'.Perm l ∧ l'.map f = m
  | [], m, perm => ⟨[], .nil, (List.Perm.eq_nil perm.symm).symm⟩
  | a :: rest, m, perm => by
      have member : f a ∈ m := perm.subset List.mem_cons_self
      obtain ⟨m₁, m₂, rfl⟩ := List.append_of_mem member
      have restPerm : (rest.map f).Perm (m₁ ++ m₂) := (perm.trans List.perm_middle).cons_inv
      obtain ⟨l'', perm'', mapped⟩ := perm_lift f rest (m₁ ++ m₂) restPerm
      obtain ⟨q₁, q₂, rfl, first, second⟩ := List.map_eq_append_iff.mp mapped
      exact ⟨q₁ ++ a :: q₂, List.perm_middle.trans (perm''.cons _), by simp [first, second]⟩

omit [DecidableEq α] in
/-- Serial runs over threads renamed by a map with the same blocks and answers. -/
theorem serial_map {γ δ : Type*} {block : γ → Multiset α → Multiset α × Bool} {answer : γ → β}
    {block' : δ → Multiset α → Multiset α × Bool} {answer' : δ → β} (f : γ → δ)
    (sameBlock : ∀ t, block' (f t) = block t) (sameAnswer : ∀ t, answer' (f t) = answer t)
    (s : Multiset α) (ts : List γ) :
    serialOutcomes block' answer' s (ts.map f) = serialOutcomes block answer s ts := by
  ext o
  constructor
  · intro path
    have lift : ∀ {x y : SConfig α δ β}, Relation.ReflTransGen (Serial block' answer') x y →
        y.pending = [] → ∀ us : List γ, us.map f = x.pending →
          Relation.ReflTransGen (Serial block answer) ⟨x.store, us, x.answers⟩ ⟨y.store, [], y.answers⟩ := by
      intro x y path finished
      induction path using Relation.ReflTransGen.head_induction_on with
      | refl =>
          intro us mapped
          rw [finished, List.map_eq_nil_iff] at mapped
          subst mapped
          exact .refl
      | head step _ later =>
          intro us mapped
          cases step with
          | @shuffle s ts ts' ans perm =>
              have mapped' : us.map f = ts := mapped
              obtain ⟨us', perm', mapped''⟩ := perm_lift f us ts' (by rw [mapped']; exact perm)
              exact .head (.shuffle perm'.symm) (later us' mapped'')
          | @run s t' rest ans =>
              have mapped' : us.map f = t' :: rest := mapped
              obtain ⟨t, us', rfl, sameHead, mappedRest⟩ := List.map_eq_cons_iff.mp mapped'
              subst sameHead
              have step := Serial.run (block := block) (answer := answer) (s := s) (t := t) (ts := us')
                (ans := ans)
              rw [← sameBlock t, ← sameAnswer t] at step
              exact .head step (later us' mappedRest)
    exact lift path rfl ts rfl
  · intro path
    have push : ∀ {x y : SConfig α γ β}, Relation.ReflTransGen (Serial block answer) x y →
        Relation.ReflTransGen (Serial block' answer') ⟨x.store, x.pending.map f, x.answers⟩
          ⟨y.store, y.pending.map f, y.answers⟩ := by
      intro x y path
      induction path with
      | refl => exact .refl
      | tail _ step earlier =>
          refine earlier.trans ?_
          cases step with
          | shuffle perm => exact .single (.shuffle (perm.map f))
          | @run s t ts ans =>
              have step := Serial.run (block := block') (answer := answer') (s := s) (t := f t)
                (ts := ts.map f) (ans := ans)
              rw [sameBlock t, sameAnswer t] at step
              exact .single step
    exact push path

/-- **A global lock around each encoded take restores exactly the serial atomic runs**: the
encodings of takes of distinct atoms, interleaved under one lock around each whole encoding, with
removal of one copy (HE's removal, not PeTTa's), have exactly the outcomes of the atomic takes fired
one after another in every order. Each encoding is one sequence of operations, so the lock may keep
every branch or commit to the first answer; a lock committed around a nondeterministic producer
keeps one answer (`PeTTaHE.Controls.once_lock_loses_answers`). -/
theorem global_lock_exact (pol : Removal) (one : pol.all = false) (s : Multiset α)
    (ts : List (Take α × β)) (linear : ∀ t ∈ ts, (t.1.take ++ t.1.read).Nodup) :
    lockedOutcomes pol s (ts.map fun t => (t.1.encode, t.2)) = serialOutcomes atomic Prod.snd s ts := by
  rw [lock_exact, serial_map (block := locked pol) (answer := Prod.snd) (fun t => (t.1.encode, t.2))
    (fun _ => rfl) (fun _ => rfl), lock_restores_serial pol one s ts linear]

/-! ## The race -/

/-- Takes `0` and `1`, makes `2`. -/
def takeAB : Take ℕ := ⟨[0, 1], [], [2]⟩
/-- Takes `1` and `0`, makes `3`: the same two atoms, removed in the other order. -/
def takeBA : Take ℕ := ⟨[1, 0], [], [3]⟩

/-- The store holding `0` and `1`. -/
def both : Multiset ℕ := {0, 1}

/-- What every serial atomic run from `both` keeps: one of `0`, `2`, `3`, and only the two
threads pending. -/
def Kept (x : SConfig ℕ (Take ℕ × ℕ) ℕ) : Prop :=
  x.store.count 0 + x.store.count 2 + x.store.count 3 = 1 ∧
    ∀ t ∈ x.pending, t = (takeAB, 1) ∨ t = (takeBA, 2)

theorem count_fire (f : Take ℕ) (s : Multiset ℕ) (x : ℕ) :
    (f.fire s).count x = s.count x - (f.take : Multiset ℕ).count x + (f.make : Multiset ℕ).count x := by
  rw [Take.fire, Multiset.count_add, Multiset.count_sub]

/-- Either take, fired, keeps the count. -/
theorem kept_fire {f : Take ℕ} (which : f = takeAB ∨ f = takeBA) {s : Multiset ℕ}
    (admitted : f.Admits s) (base : s.count 0 + s.count 2 + s.count 3 = 1) :
    (f.fire s).count 0 + (f.fire s).count 2 + (f.fire s).count 3 = 1 := by
  have zero := Multiset.count_le_of_le 0 (Take.take_le admitted)
  rw [count_fire, count_fire, count_fire]
  rcases which with rfl | rfl
  · have t0 : ((takeAB.take : List ℕ) : Multiset ℕ).count 0 = 1 := by decide
    have t2 : ((takeAB.take : List ℕ) : Multiset ℕ).count 2 = 0 := by decide
    have t3 : ((takeAB.take : List ℕ) : Multiset ℕ).count 3 = 0 := by decide
    have m0 : ((takeAB.make : List ℕ) : Multiset ℕ).count 0 = 0 := by decide
    have m2 : ((takeAB.make : List ℕ) : Multiset ℕ).count 2 = 1 := by decide
    have m3 : ((takeAB.make : List ℕ) : Multiset ℕ).count 3 = 0 := by decide
    rw [t0, t2, t3, m0, m2, m3]
    rw [t0] at zero
    omega
  · have t0 : ((takeBA.take : List ℕ) : Multiset ℕ).count 0 = 1 := by decide
    have t2 : ((takeBA.take : List ℕ) : Multiset ℕ).count 2 = 0 := by decide
    have t3 : ((takeBA.take : List ℕ) : Multiset ℕ).count 3 = 0 := by decide
    have m0 : ((takeBA.make : List ℕ) : Multiset ℕ).count 0 = 0 := by decide
    have m2 : ((takeBA.make : List ℕ) : Multiset ℕ).count 2 = 0 := by decide
    have m3 : ((takeBA.make : List ℕ) : Multiset ℕ).count 3 = 1 := by decide
    rw [t0, t2, t3, m0, m2, m3]
    rw [t0] at zero
    omega

theorem kept_step {x y : SConfig ℕ (Take ℕ × ℕ) ℕ} (kept : Kept x)
    (step : Serial atomic Prod.snd x y) : Kept y := by
  obtain ⟨counts, pending⟩ := kept
  cases step with
  | shuffle perm => exact ⟨counts, fun t member => pending t (perm.symm.subset member)⟩
  | @run s t ts ans =>
      have base : s.count 0 + s.count 2 + s.count 3 = 1 := counts
      refine ⟨?_, fun u member => pending u (List.mem_cons_of_mem t member)⟩
      show (t.1.block s).1.count 0 + (t.1.block s).1.count 2 + (t.1.block s).1.count 3 = 1
      unfold Take.block
      split_ifs with admitted
      · have which : t.1 = takeAB ∨ t.1 = takeBA := by
          rcases pending t List.mem_cons_self with same | same
          · exact Or.inl (by rw [same])
          · exact Or.inr (by rw [same])
        exact kept_fire which admitted base
      · exact base

theorem kept_reach {x y : SConfig ℕ (Take ℕ × ℕ) ℕ}
    (path : Relation.ReflTransGen (Serial atomic Prod.snd) x y) (kept : Kept x) : Kept y := by
  induction path with
  | refl => exact kept
  | tail _ step earlier => exact kept_step earlier step

/-- The two threads, atomic. -/
def threads : List (Take ℕ × ℕ) := [(takeAB, 1), (takeBA, 2)]

theorem kept_start : Kept ⟨both, threads, 0⟩ := by
  refine ⟨by decide, ?_⟩
  intro t member
  simp only [threads, List.mem_cons, List.not_mem_nil, or_false] at member
  exact member

/-- **The race.** For every removal policy, the interleaved encodings of two takes of the same two
atoms reach an outcome that no sequence of atomic firings produces. -/
theorem race (pol : Removal) :
    ∃ o ∈ interleavedOutcomes pol both (threads.map fun t => (t.1.encode, t.2)),
      o ∉ serialOutcomes atomic Prod.snd both threads := by
  have q1 : (Op.query [0, 1]).run pol both = some both := run_query_pass pol (by decide)
  have q2 : (Op.query [1, 0]).run pol both = some both := run_query_pass pol (by decide)
  have r1 : (Op.remove 1).run pol both = some {0} :=
    (run_remove_present pol (by decide) (fun _ => by decide)).trans (by decide)
  have r0 : (Op.remove 0).run pol ({0} : Multiset ℕ) = some 0 :=
    (run_remove_present pol (by decide) (fun _ => by decide)).trans (by decide)
  have common : Relation.ReflTransGen (Interleave pol)
      ⟨both, threads.map (fun t => (t.1.encode, t.2)), 0⟩
      ⟨0, ([Op.remove 1, Op.add 2], 1) :: ([Op.remove 0, Op.add 3], 2) :: [], 0⟩ :=
    .head (.op q1) <| .head (.shuffle (.swap _ _ _)) <| .head (.op q2) <| .head (.op r1) <|
      .head (.shuffle (.swap _ _ _)) <| .single (.op r0)
  have notKept : ∀ s' : Multiset ℕ, s'.count 0 + s'.count 2 + s'.count 3 ≠ 1 →
      ∀ A : Multiset ℕ, (A, s') ∉ serialOutcomes atomic Prod.snd both threads :=
    fun s' bad A path => bad (kept_reach path kept_start).1
  cases checked : pol.checked
  · -- unchecked removals: both threads go on, both answer, both outputs are made
    have a1 : (Op.remove 1).run pol (0 : Multiset ℕ) = some 0 := by
      rw [run_remove_absent pol (by decide)]; simp [checked]
    have a0 : (Op.remove 0).run pol ({2} : Multiset ℕ) = some {2} := by
      rw [run_remove_absent pol (by decide)]; simp [checked]
    refine ⟨({2, 1}, {3, 2}), common.trans ?_, notKept _ (by decide) _⟩
    exact .head (.op a1) <| .head (.op rfl) <| .head .finish <| .head (.op a0) <|
      .head (.op rfl) <| .single .finish
  · -- checked removals: both threads die, both atoms are lost, nothing is made
    have d1 : (Op.remove 1).run pol (0 : Multiset ℕ) = none := by
      rw [run_remove_absent pol (by decide)]; simp [checked]
    have d0 : (Op.remove 0).run pol (0 : Multiset ℕ) = none := by
      rw [run_remove_absent pol (by decide)]; simp [checked]
    refine ⟨(0, 0), common.trans ?_, notKept _ (by decide) _⟩
    exact .head (.die d1) <| .single (.die d0)

/-! ## Absence in a snapshot races too -/

theorem run_query_fail (pol : Removal) {l : List α} {s : Multiset α} (missing : ¬ ∀ a ∈ l, a ∈ s) :
    (Op.query l).run pol s = none := by
  simp only [Op.run, if_neg missing]

theorem run_add (pol : Removal) (a : α) (s : Multiset α) : (Op.add a).run pol s = some (a ::ₘ s) := rfl

omit [DecidableEq α] in
theorem perm_pair {γ : Type*} {a b : γ} (ne : a ≠ b) : ∀ {l : List γ}, l.Perm [a, b] → l = [a, b] ∨ l = [b, a]
  | [], perm => absurd perm.length_eq (by simp)
  | [_], perm => absurd perm.length_eq (by simp)
  | _ :: _ :: _ :: _, perm => absurd perm.length_eq (by simp)
  | [x, y], perm => by
      have hx : x ∈ [a, b] := perm.subset (by simp)
      have hy : y ∈ [a, b] := perm.subset (by simp)
      have nodup : [x, y].Nodup := perm.nodup_iff.mpr (by simp [ne])
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx hy
      simp only [List.nodup_cons, List.mem_singleton, List.not_mem_nil, not_false_eq_true,
        List.nodup_nil, and_true] at nodup
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
      · exact absurd rfl nodup
      · exact Or.inl rfl
      · exact Or.inr rfl
      · exact absurd rfl nodup

/-- Adds `1`, reads `2`, adds `3`; answers `1`. It never removes. -/
def writeA : List (Op ℕ) × ℕ := ([.add 1, .query [2], .add 3], 1)
/-- Adds `2`, reads `1`, adds `4`; answers `2`. It never removes. -/
def writeB : List (Op ℕ) × ℕ := ([.add 2, .query [1], .add 4], 2)

theorem writeA_ne_writeB : writeA ≠ writeB := fun same => absurd (congrArg Prod.snd same) (by decide)

theorem runA_empty (pol : Removal) : runOps pol writeA.1 0 = (1 ::ₘ 0, false) := by
  rw [show writeA.1 = [.add 1, .query [2], .add 3] from rfl, runOps_cons_some (run_add pol 1 0),
    runOps_cons_none (run_query_fail pol (l := [2]) (s := 1 ::ₘ 0) (by decide))]

theorem runB_empty (pol : Removal) : runOps pol writeB.1 0 = (2 ::ₘ 0, false) := by
  rw [show writeB.1 = [.add 2, .query [1], .add 4] from rfl, runOps_cons_some (run_add pol 2 0),
    runOps_cons_none (run_query_fail pol (l := [1]) (s := 2 ::ₘ 0) (by decide))]

theorem runB_after (pol : Removal) : runOps pol writeB.1 (1 ::ₘ 0) = (4 ::ₘ 2 ::ₘ 1 ::ₘ 0, true) := by
  rw [show writeB.1 = [.add 2, .query [1], .add 4] from rfl, runOps_cons_some (run_add pol 2 _),
    runOps_cons_some (run_query_pass pol (l := [1]) (s := 2 ::ₘ 1 ::ₘ 0) (by decide)),
    runOps_cons_some (run_add pol 4 _)]
  rfl

theorem runA_after (pol : Removal) : runOps pol writeA.1 (2 ::ₘ 0) = (3 ::ₘ 1 ::ₘ 2 ::ₘ 0, true) := by
  rw [show writeA.1 = [.add 1, .query [2], .add 3] from rfl, runOps_cons_some (run_add pol 1 _),
    runOps_cons_some (run_query_pass pol (l := [2]) (s := 1 ::ₘ 2 ::ₘ 0) (by decide)),
    runOps_cons_some (run_add pol 3 _)]
  rfl

/-- What every sequential run of the two writers keeps: at most one of them answers. -/
def OneWriter (x : SConfig ℕ (List (Op ℕ) × ℕ) ℕ) : Prop :=
  (x.store = 0 ∧ x.pending.Perm [writeA, writeB] ∧ x.answers = 0) ∨
    (x.store = 1 ::ₘ 0 ∧ x.pending = [writeB] ∧ x.answers = 0) ∨
    (x.store = 2 ::ₘ 0 ∧ x.pending = [writeA] ∧ x.answers = 0) ∨
    (x.pending = [] ∧ x.answers.card = 1)

theorem oneWriter_step (pol : Removal) {x y : SConfig ℕ (List (Op ℕ) × ℕ) ℕ} (kept : OneWriter x)
    (step : Serial (bodies pol) Prod.snd x y) : OneWriter y := by
  cases step with
  | @shuffle s ts ts' ans perm =>
      rcases kept with ⟨hs, hp, ha⟩ | ⟨hs, hp, ha⟩ | ⟨hs, hp, ha⟩ | ⟨hp, ha⟩
      · exact Or.inl ⟨hs, perm.symm.trans hp, ha⟩
      · have hp : ts = [writeB] := hp
        subst hp
        exact Or.inr (Or.inl ⟨hs, List.perm_singleton.mp perm.symm, ha⟩)
      · have hp : ts = [writeA] := hp
        subst hp
        exact Or.inr (Or.inr (Or.inl ⟨hs, List.perm_singleton.mp perm.symm, ha⟩))
      · have hp : ts = [] := hp
        subst hp
        exact Or.inr (Or.inr (Or.inr ⟨List.Perm.eq_nil perm.symm, ha⟩))
  | @run s t ts ans =>
      rcases kept with ⟨hs, hp, ha⟩ | ⟨hs, hp, ha⟩ | ⟨hs, hp, ha⟩ | ⟨hp, ha⟩
      · have hs : s = 0 := hs
        have ha : ans = 0 := ha
        subst hs ha
        rcases perm_pair writeA_ne_writeB hp with same | same
        · obtain ⟨rfl, rfl⟩ := List.cons.inj same
          refine Or.inr (Or.inl ⟨?_, rfl, ?_⟩)
          · show (runOps pol writeA.1 0).1 = _
            rw [runA_empty]
          · show (if (runOps pol writeA.1 0).2 then writeA.2 ::ₘ 0 else 0) = 0
            rw [runA_empty]
            rfl
        · obtain ⟨rfl, rfl⟩ := List.cons.inj same
          refine Or.inr (Or.inr (Or.inl ⟨?_, rfl, ?_⟩))
          · show (runOps pol writeB.1 0).1 = _
            rw [runB_empty]
          · show (if (runOps pol writeB.1 0).2 then writeB.2 ::ₘ 0 else 0) = 0
            rw [runB_empty]
            rfl
      · have hs : s = 1 ::ₘ 0 := hs
        have hp : t :: ts = [writeB] := hp
        have ha : ans = 0 := ha
        subst hs ha
        obtain ⟨rfl, rfl⟩ := List.cons.inj hp
        refine Or.inr (Or.inr (Or.inr ⟨rfl, ?_⟩))
        show (if (runOps pol writeB.1 (1 ::ₘ 0)).2 then writeB.2 ::ₘ 0 else 0).card = 1
        rw [runB_after]
        rfl
      · have hs : s = 2 ::ₘ 0 := hs
        have hp : t :: ts = [writeA] := hp
        have ha : ans = 0 := ha
        subst hs ha
        obtain ⟨rfl, rfl⟩ := List.cons.inj hp
        refine Or.inr (Or.inr (Or.inr ⟨rfl, ?_⟩))
        show (if (runOps pol writeA.1 (2 ::ₘ 0)).2 then writeA.2 ::ₘ 0 else 0).card = 1
        rw [runA_after]
        rfl
      · exact absurd hp (List.cons_ne_nil t ts)

/-- **Absence in a snapshot races too.** Two threads that never remove anything, each adding an atom
and then matching the other's, answer both under interleaving; one after the other, at most one
answers. A match that comes back empty observes absence in its snapshot, so even reading and adding
needs coordination in PeTTa; the coordination-free fragment is the one whose reads wait for their
atoms, the step's monotone rules (`MonotoneInference.confluent`). -/
theorem snapshot_absence_races (pol : Removal) :
    ∃ o ∈ interleavedOutcomes pol 0 [writeA, writeB],
      o ∉ serialOutcomes (bodies pol) Prod.snd 0 [writeA, writeB] := by
  have q2 : (Op.query [2]).run pol (2 ::ₘ 1 ::ₘ 0 : Multiset ℕ) = some (2 ::ₘ 1 ::ₘ 0) :=
    run_query_pass pol (by decide)
  have q1 : (Op.query [1]).run pol (3 ::ₘ 2 ::ₘ 1 ::ₘ 0 : Multiset ℕ) = some (3 ::ₘ 2 ::ₘ 1 ::ₘ 0) :=
    run_query_pass pol (by decide)
  refine ⟨(2 ::ₘ 1 ::ₘ 0, 4 ::ₘ 3 ::ₘ 2 ::ₘ 1 ::ₘ 0), ?_, ?_⟩
  · exact .head (.op (run_add pol 1 0)) <| .head (.shuffle (.swap _ _ _)) <|
      .head (.op (run_add pol 2 _)) <| .head (.shuffle (.swap _ _ _)) <| .head (.op q2) <|
      .head (.op (run_add pol 3 _)) <| .head .finish <| .head (.op q1) <|
      .head (.op (run_add pol 4 _)) <| .single .finish
  · intro path
    have reach : ∀ {x y : SConfig ℕ (List (Op ℕ) × ℕ) ℕ},
        Relation.ReflTransGen (Serial (bodies pol) Prod.snd) x y → OneWriter x → OneWriter y := by
      intro x y path kept
      induction path with
      | refl => exact kept
      | tail _ step earlier => exact oneWriter_step pol earlier step
    have final := reach path (Or.inl ⟨rfl, .refl _, rfl⟩)
    rcases final with ⟨_, hp, _⟩ | ⟨_, hp, _⟩ | ⟨_, hp, _⟩ | ⟨_, ha⟩
    · exact absurd hp.length_eq (by simp)
    · exact absurd hp (by simp)
    · exact absurd hp (by simp)
    · exact absurd ha (by decide)

/-! ## Atomic firings on the step -/

open GuardFreeProcessOrders in
/-- **Atomic firings with non-interfering footprints run in parallel**, keeping a serial meaning:
on the step, for every substitution action, the two orders of two check-free independent firings
both run and end in the same configuration up to solutions. -/
theorem atomic_parallel {T S O : Type*} [DecidableEq O] (A : SubstitutionAction T S) (label : O → T)
    {f g : ConditionalSchedule.Firing T O} {C : Configuration T O}
    (fFree : f.1.checks = []) (gFree : g.1.checks = []) (noCause : NoCause f g) (noAsym : NoAsym f g)
    (noReuse : NoReuse f g) (first : f.2.Valid A label f.1 C)
    (second : g.2.Valid A label g.1 (f.2.result label f.1 C)) :
    g.2.Valid A label g.1 C ∧ f.2.Valid A label f.1 (g.2.result label g.1 C) ∧
      SameUpTo A (g.2.result label g.1 (f.2.result label f.1 C))
        (f.2.result label f.1 (g.2.result label g.1 C)) :=
  FragmentsOfTheStep.LinearTake.linearTake_interchange A label fFree gFree noCause noAsym noReuse
    first second

/-! ## Controls -/

namespace Controls

/-- A take of two copies of `0`, making `1`. -/
def twice : Take ℕ := ⟨[0, 0], [], [1]⟩

/-- **Negative control: repeated atoms.** Even without interruption, the encoding of a take of two
copies of `0` from a store holding one is not the take: the match does not count copies. The take
is refused and keeps the store; the encoding removes the copy. -/
theorem repeated_atom_inexact (pol : Removal) :
    ¬ twice.Admits {0} ∧ twice.block {0} = ({0}, false) ∧ (runOps pol twice.encode {0}).1 ≠ {0} := by
  have refused : ¬ twice.Admits {0} := by decide
  refine ⟨refused, by rw [Take.block, if_neg refused], ?_⟩
  have q : (Op.query [0, 0]).run pol ({0} : Multiset ℕ) = some {0} := run_query_pass pol (by decide)
  have r : (Op.remove 0).run pol ({0} : Multiset ℕ) = some 0 :=
    (run_remove_present pol (by decide) (fun _ => by decide)).trans (by decide)
  have again : (Op.remove 0).run pol (0 : Multiset ℕ) = if pol.checked then none else some 0 :=
    run_remove_absent pol (by decide)
  have code : twice.encode = [Op.query [0, 0], Op.remove 0, Op.remove 0, Op.add 1] := rfl
  rw [code, runOps_cons_some q, runOps_cons_some r]
  cases checked : pol.checked
  · have goes : (Op.remove 0).run pol (0 : Multiset ℕ) = some 0 := by rw [again]; simp [checked]
    rw [runOps_cons_some goes,
      runOps_cons_some (show (Op.add 1).run pol (0 : Multiset ℕ) = some {1} from rfl)]
    show ({1} : Multiset ℕ) ≠ {0}
    decide
  · have dies : (Op.remove 0).run pol (0 : Multiset ℕ) = none := by rw [again]; simp [checked]
    rw [runOps_cons_none dies]
    decide

/-- A take of one copy of `0`, making `1`. -/
def once : Take ℕ := ⟨[0], [], [1]⟩

/-- **Negative control: removal of every copy.** From a store holding two copies of `0`, the take
leaves one; PeTTa's removal leaves none. HE's removal of one copy agrees with the take. -/
theorem remove_all_loses_copy :
    once.block {0, 0} = ({1, 0}, true) ∧
      (runOps ⟨true, true⟩ once.encode {0, 0}).1 = {1} ∧
      runOps ⟨false, true⟩ once.encode {0, 0} = once.block {0, 0} := by
  refine ⟨by decide, by decide, ?_⟩
  exact sequential_exact _ once {0, 0} (by decide) (fun h => absurd h (by decide))

/-- A taker of `0` making `1`, and one making `2`. -/
def toOne : Take ℕ := ⟨[0], [], [1]⟩
def toTwo : Take ℕ := ⟨[0], [], [2]⟩

/-- **Control: conflict is a choice.** Both takers are admitted at `{0}`, neither after the other;
the two serial outcomes differ, and each is reached. -/
theorem conflict_is_choice :
    toOne.Admits {0} ∧ toTwo.Admits {0} ∧ ¬ toTwo.Admits (toOne.fire {0}) ∧
      ¬ toOne.Admits (toTwo.fire {0}) ∧ toOne.fire {0} ≠ toTwo.fire {0} ∧
      (({1}, {1}) : Multiset ℕ × Multiset ℕ) ∈
        serialOutcomes atomic Prod.snd {0} [(toOne, 1), (toTwo, 2)] ∧
      (({2}, {2}) : Multiset ℕ × Multiset ℕ) ∈
        serialOutcomes atomic Prod.snd {0} [(toOne, 1), (toTwo, 2)] := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, ?_, ?_⟩
  · have fires : atomic (toOne, 1) ({0} : Multiset ℕ) = ({1}, true) := by decide
    have refused : atomic (toTwo, 2) ({1} : Multiset ℕ) = ({1}, false) := by decide
    exact .head (serial_run_eq fires) (.head (serial_run_eq refused) .refl)
  · have fires : atomic (toTwo, 2) ({0} : Multiset ℕ) = ({2}, true) := by decide
    have refused : atomic (toOne, 1) ({2} : Multiset ℕ) = ({2}, false) := by decide
    exact .head (Serial.shuffle (.swap _ _ _))
      (.head (serial_run_eq fires) (.head (serial_run_eq refused) .refl))

end Controls

#print axioms Take.fire_comm
#print axioms sequential_exact
#print axioms lock_restores_serial
#print axioms lock_exact
#print axioms global_lock_exact
#print axioms serial_sub_interleaved
#print axioms race
#print axioms snapshot_absence_races
#print axioms atomic_parallel
#print axioms Controls.repeated_atom_inexact
#print axioms Controls.remove_all_loses_copy
#print axioms Controls.conflict_is_choice

end Concurrency

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies
