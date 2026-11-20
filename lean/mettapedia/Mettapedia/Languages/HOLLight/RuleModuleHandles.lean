/-!
# Handles of a compiled rule module in CeTTa

A rule module compiled to C runs in CeTTa as a native module (`rcm_cetta.c`).  Its host keeps
values of the module across calls under handles: `OPS hold TERM` (and `OPS call-hold`) builds a
value in the module's interning store and answers a handle, a number; `OPS view` and every term
that names the handle `(TAG:handle N)` read the kept value back; `OPS release` stops keeping it;
`OPS reset` refuses every handle and frees the store.  This file models the handle table as a
state machine and proves the laws the host promises.

* **The model.**  An entry (`Held`, `RcmHeld`) holds a value, its sort, the epoch of the store it
  was made in and whether it is live; the state (`State`) is the entries in the order they were
  made (`rcm_held`, the index is the handle), the epoch of the store (`rc_intern_epoch`) and
  whether the store is active (`active` in `rc_intern.c`).  A handle answers (`lookup`,
  `rcm_held_valid`) when it is in range, live and of the current epoch; with a sort expected it
  answers only a value of that sort (`lookupSort`).  The operations (`Op`, `step`): a hold (`hold`,
  `rcm_hold` after the run that builds the value, `rc_intern_begin`); a release (marks a valid
  handle not live; any other handle is refused as stale and nothing changes); a reset (every entry
  marked not live, `killAll`, then `rc_intern_free` when the module has interned sorts: when the
  store is active the epoch moves on); a call (a run, at whose end `rc_intern_end` frees the store
  when it is above its keep size and no handle is valid); a call stopped by a refinement violation
  (the store freed when the module has interned sorts).  The flag `interned` is `rcm_interned`:
  the module has a sort of representation 5 or 6.
* **The laws.**  A hold answers a handle that answers its value (`hold_answers`): existence.  A
  released handle is refused (`release_refuses`), a never-issued id is refused
  (`lookup_out_of_range`), and after a reset every handle is refused, whether or not the module has
  interned sorts (`reset_refuses`, `reset_dead`); after a call stopped by a refinement violation of
  a module with interned sorts every handle is refused too (`stop_refuses`).  A refused handle that
  was issued stays refused through every later run of operations (`dead_run`): the store's epoch
  never goes back and an entry is never made live again.  Ids are never reused: every later hold
  answers a larger id (`later_hold_id`).  A value held later gets a new handle, and an old handle
  answers its own value or nothing, never a later one (`old_handle_answers_own`,
  `old_handle_not_newer`).

What the model leaves out.

* The values themselves: a kept value is a `V`; that the interning store keeps the value of a
  valid handle (the collector marks the values of valid handles as roots, `rcm_held_roots`) is
  trusted, as is the reading and writing of atoms.  A reset also clears the value of every entry
  (`value = NULL`); the model keeps it, since no operation reads the value of an entry that is not
  live.
* The size of the store: whether a run ends above `RC_INTERN_KEEP_BYTES` is an input of `call`.
  Stores made fresh at every run (`rc_intern_fresh`) are not used by this host.  A hold's end never
  frees the store, since the handle it has just made is valid.
* Holds and calls refused before they run (a stale handle in the term, a sort mismatch, a judgment
  whose values do not outlive a call) change nothing and are not operations here; `lookup` and
  `lookupSort` are the checks they make.  Statistics, captures and relation rows are left out.
* Ids and epochs are naturals; the C's `size_t` and `uint64_t` never wrap in practice.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.RuleModuleHandles

universe u v

variable {V : Type u} {S : Type v}

/-- `RcmHeld`: a kept value, its sort, the epoch of the store it was made in, and whether it is
still kept (`live`). -/
structure Held (V : Type u) (S : Type v) where
  /-- The value. -/
  value : V
  /-- Its sort. -/
  sort : S
  /-- `rc_intern_epoch()` when it was kept. -/
  epoch : Nat
  /-- Not released. -/
  live : Bool

/-- The host's table and the store's life. -/
structure State (V : Type u) (S : Type v) where
  /-- `rcm_held`: the entries, the handle of each being its index. -/
  held : List (Held V S)
  /-- `rc_intern_epoch()`. -/
  epoch : Nat
  /-- `active` of `rc_intern.c`: a store exists. -/
  active : Bool

/-- The state before any operation. -/
def State.init : State V S := ⟨[], 0, false⟩

/-- `rcm_held_valid(i)` and the read of a handle: the kept value and its sort when the handle is
in range, live and of the current epoch; otherwise refused (`"stale handle"`). -/
def lookup (st : State V S) (i : Nat) : Option (V × S) :=
  match st.held[i]? with
  | some h => if h.live = true ∧ h.epoch = st.epoch then some (h.value, h.sort) else none
  | none => none

/-- A handle read where a value of the sort `s` is expected: refused unless it holds a value of
that sort (`"handle N holds a value of sort ..."`). -/
def lookupSort [DecidableEq S] (st : State V S) (i : Nat) (s : S) : Option V :=
  match lookup st i with
  | some (x, s') => if s' = s then some x else none
  | none => none

/-- An entry valid in the state. -/
def Held.valid (st : State V S) (h : Held V S) : Prop := h.live = true ∧ h.epoch = st.epoch

/-- `rc_intern_begin`, at the start of every run of a module with interned sorts: the store
becomes active (an active store is kept). -/
def beginRun (interned : Bool) (st : State V S) : State V S :=
  if interned then { st with active := true } else st

/-- `rc_intern_free`: when the store is active it is freed and the epoch moves on. -/
def free (st : State V S) : State V S :=
  if st.active then { st with epoch := st.epoch + 1, active := false } else st

/-- `rcm_hold`: a new entry at the end, of the current epoch, live; its index is the handle. -/
def push (st : State V S) (x : V) (s : S) : State V S :=
  { st with held := st.held ++ [⟨x, s, st.epoch, true⟩] }

/-- The entries with the `i`-th one not live (`rcm_held[h].live = false`). -/
def releaseAt : List (Held V S) → Nat → List (Held V S)
  | [], _ => []
  | h :: hs, 0 => { h with live := false } :: hs
  | h :: hs, i + 1 => h :: releaseAt hs i

/-- The entries all made not live: the loop of `OPS reset`. -/
def killAll (hs : List (Held V S)) : List (Held V S) := hs.map fun h => { h with live := false }

/-- Some handle answers (`rcm_held_roots(NULL) > 0`). -/
def anyValid (st : State V S) : Prop := ∃ h ∈ st.held, h.valid st

/-- The operations of the host. -/
inductive Op (V : Type u) (S : Type v)
  /-- `OPS hold` or `OPS call-hold`: a run builds the value, which is then kept. -/
  | hold (x : V) (s : S)
  /-- `OPS release HANDLE`. -/
  | release (i : Nat)
  /-- `OPS reset`: every handle refused, then the store freed. -/
  | reset
  /-- `OPS call`: a run; `big` says whether the store is above its keep size at its end. -/
  | call (big : Bool)
  /-- A run stopped by a refinement violation. -/
  | stop

open Classical in
/-- One operation.  `interned` is `rcm_interned`. -/
noncomputable def step (interned : Bool) (st : State V S) : Op V S → State V S
  | .hold x s => push (beginRun interned st) x s
  | .release i =>
    if (lookup st i).isSome then { st with held := releaseAt st.held i } else st
  | .reset =>
    if interned then free { st with held := killAll st.held } else { st with held := killAll st.held }
  | .call big =>
    if interned = true ∧ big = true ∧ ¬ anyValid (beginRun interned st) then
      free (beginRun interned st)
    else beginRun interned st
  | .stop => if interned then free (beginRun interned st) else st

/-- A run of operations. -/
noncomputable def run (interned : Bool) : State V S → List (Op V S) → State V S
  | st, [] => st
  | st, op :: ops => run interned (step interned st op) ops

/-! ## Reading entries -/

theorem lookup_eq_some_iff {st : State V S} {i : Nat} {x : V} {s : S} :
    lookup st i = some (x, s) ↔
      ∃ h, st.held[i]? = some h ∧ h.valid st ∧ h.value = x ∧ h.sort = s := by
  unfold lookup
  cases e : st.held[i]? with
  | none => simp
  | some h =>
    simp only [Option.some.injEq, Held.valid]
    split
    · rename_i hv
      simp only [Option.some.injEq, Prod.mk.injEq]
      exact ⟨fun ⟨h₁, h₂⟩ => ⟨h, rfl, hv, h₁, h₂⟩, fun ⟨_, e', _, h₁, h₂⟩ => by subst e'; exact ⟨h₁, h₂⟩⟩
    · rename_i hv
      exact ⟨nofun, fun ⟨_, e', hv', _⟩ => by subst e'; exact absurd hv' hv⟩

/-- **A never-issued id is refused.** -/
theorem lookup_out_of_range {st : State V S} {i : Nat} (h : st.held.length ≤ i) :
    lookup st i = none := by
  unfold lookup
  rw [List.getElem?_eq_none h]

theorem length_releaseAt : ∀ (hs : List (Held V S)) (i : Nat), (releaseAt hs i).length = hs.length
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: hs, i + 1 => congrArg (· + 1) (length_releaseAt hs i)

theorem getElem?_releaseAt : ∀ (hs : List (Held V S)) (i j : Nat),
    (releaseAt hs i)[j]? = (hs[j]?).map fun h => if j = i then { h with live := false } else h
  | [], _, _ => rfl
  | h :: hs, 0, 0 => by simp [releaseAt]
  | h :: hs, 0, j + 1 => by simp [releaseAt]
  | h :: hs, i + 1, 0 => by simp [releaseAt]
  | h :: hs, i + 1, j + 1 => by
    simp only [releaseAt, List.getElem?_cons_succ]
    rw [getElem?_releaseAt hs i j]
    simp

/-! ## Holds answer their values -/

/-- The handle a hold answers: the number of entries before it. -/
def holdId (st : State V S) : Nat := st.held.length

/-- **A hold always answers a handle that answers its value** (and its sort). -/
theorem hold_answers (interned : Bool) (st : State V S) (x : V) (s : S) :
    lookup (step interned st (.hold x s)) (holdId st) = some (x, s) := by
  have e : (beginRun interned st).held = st.held := by unfold beginRun; split <;> rfl
  have ee : (beginRun interned st).epoch = st.epoch := by unfold beginRun; split <;> rfl
  simp only [step, push, lookup, holdId]
  rw [e, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
  simp [ee]

theorem hold_answers_sort [DecidableEq S] (interned : Bool) (st : State V S) (x : V) (s : S) :
    lookupSort (step interned st (.hold x s)) (holdId st) s = some x := by
  simp [lookupSort, hold_answers]

/-! ## Releases -/

/-- **A released handle is refused.** -/
theorem release_refuses (interned : Bool) (st : State V S) (i : Nat) :
    lookup (step interned st (.release i)) i = none := by
  simp only [step]
  split
  · unfold lookup
    simp only
    rw [getElem?_releaseAt]
    cases st.held[i]? with
    | none => rfl
    | some h => simp
  · rename_i h
    simpa using h

/-! ## Refusal is final -/

/-- A handle that was issued and is refused: released, or of an older store. -/
def Dead (st : State V S) (i : Nat) : Prop := i < st.held.length ∧ lookup st i = none

theorem dead_iff {st : State V S} {i : Nat} :
    Dead st i ↔ ∃ h, st.held[i]? = some h ∧ ¬ h.valid st := by
  unfold Dead lookup Held.valid
  constructor
  · rintro ⟨hi, hl⟩
    rw [List.getElem?_eq_getElem hi] at hl ⊢
    refine ⟨_, rfl, fun hv => ?_⟩
    simp only [if_pos hv] at hl
    exact absurd hl nofun
  · rintro ⟨h, e, hv⟩
    refine ⟨(List.getElem?_eq_some_iff.mp e).1, ?_⟩
    rw [e]
    simp only [if_neg hv]

/-- The epoch of the store never goes back. -/
theorem epoch_le_step (interned : Bool) (st : State V S) (op : Op V S) :
    st.epoch ≤ (step interned st op).epoch := by
  have hb : (beginRun interned st).epoch = st.epoch := by unfold beginRun; split <;> rfl
  have hf : ∀ t : State V S, t.epoch ≤ (free t).epoch := by
    intro t; unfold free; split
    · exact Nat.le_succ _
    · exact Nat.le_refl _
  cases op with
  | hold x s => simp only [step, push]; rw [hb]; exact Nat.le_refl _
  | release i => simp only [step]; split <;> exact Nat.le_refl _
  | reset =>
    simp only [step]
    split
    · exact hf { st with held := killAll st.held }
    · exact Nat.le_refl _
  | call big =>
    simp only [step]
    split
    · exact hb ▸ hf _
    · rw [hb]; exact Nat.le_refl _
  | stop =>
    simp only [step]
    split
    · exact hb ▸ hf _
    · exact Nat.le_refl _

/-- An entry is kept by every operation: the same value, sort and epoch, live only if it was. -/
theorem entry_step (interned : Bool) (st : State V S) (op : Op V S) {i : Nat} {h : Held V S}
    (e : st.held[i]? = some h) :
    ∃ h', (step interned st op).held[i]? = some h' ∧ h'.value = h.value ∧ h'.sort = h.sort ∧
      h'.epoch = h.epoch ∧ (h'.live = true → h.live = true) := by
  have hb : (beginRun interned st).held = st.held := by unfold beginRun; split <;> rfl
  have hf : ∀ t : State V S, (free t).held = t.held := by intro t; unfold free; split <;> rfl
  have same : ∀ t : State V S, t.held = st.held →
      ∃ h', t.held[i]? = some h' ∧ h'.value = h.value ∧ h'.sort = h.sort ∧ h'.epoch = h.epoch ∧
        (h'.live = true → h.live = true) :=
    fun t ht => ⟨h, by rw [ht, e], rfl, rfl, rfl, id⟩
  cases op with
  | hold x s =>
    refine ⟨h, ?_, rfl, rfl, rfl, id⟩
    simp only [step, push]
    rw [hb, List.getElem?_append_left (List.getElem?_eq_some_iff.mp e).1, e]
  | release j =>
    simp only [step]
    split
    · simp only
      rw [getElem?_releaseAt, e]
      by_cases hij : i = j
      · exact ⟨_, rfl, by simp [hij], by simp [hij], by simp [hij], by simp [hij]⟩
      · exact ⟨_, rfl, by simp [hij], by simp [hij], by simp [hij], by simp [hij]⟩
    · exact same _ rfl
  | reset =>
    have hk : (killAll st.held)[i]? = some { h with live := false } := by
      simp only [killAll, List.getElem?_map, e, Option.map_some]
    refine ⟨{ h with live := false }, ?_, rfl, rfl, rfl, fun h' => by simp at h'⟩
    simp only [step]
    split
    · rw [hf]
      exact hk
    · exact hk
  | call big =>
    simp only [step]
    split
    · exact same _ ((hf _).trans hb)
    · exact same _ hb
  | stop =>
    simp only [step]
    split
    · exact same _ ((hf _).trans hb)
    · exact same _ rfl

theorem length_step (interned : Bool) (st : State V S) (op : Op V S) :
    st.held.length ≤ (step interned st op).held.length := by
  have hb : (beginRun interned st).held = st.held := by unfold beginRun; split <;> rfl
  have hf : ∀ t : State V S, (free t).held = t.held := by intro t; unfold free; split <;> rfl
  cases op with
  | hold x s => simp only [step, push, hb, List.length_append]; omega
  | release j =>
    simp only [step]
    split
    · simp only [length_releaseAt, Nat.le_refl]
    · exact Nat.le_refl _
  | reset =>
    simp only [step]
    split
    · rw [hf]
      simp only [killAll, List.length_map, Nat.le_refl]
    · simp only [killAll, List.length_map, Nat.le_refl]
  | call big =>
    simp only [step]
    split
    · rw [hf, hb]; exact Nat.le_refl _
    · rw [hb]; exact Nat.le_refl _
  | stop =>
    simp only [step]
    split
    · rw [hf, hb]; exact Nat.le_refl _
    · exact Nat.le_refl _

/-- **The epoch invariant**: no entry is of a later store than the current one. -/
def EpochsLe (st : State V S) : Prop := ∀ h ∈ st.held, h.epoch ≤ st.epoch

theorem epochsLe_init : EpochsLe (State.init : State V S) := fun _ h => absurd h List.not_mem_nil

theorem epochsLe_releaseAt {e : Nat} : ∀ (hs : List (Held V S)) (i : Nat),
    (∀ h ∈ hs, h.epoch ≤ e) → ∀ h ∈ releaseAt hs i, h.epoch ≤ e
  | [], _, _ => fun _ h => absurd h List.not_mem_nil
  | h :: hs, 0, H => by
    intro h' hh'
    simp only [releaseAt, List.mem_cons] at hh'
    rcases hh' with rfl | hh'
    · exact H h List.mem_cons_self
    · exact H h' (List.mem_cons_of_mem _ hh')
  | h :: hs, i + 1, H => by
    intro h' hh'
    simp only [releaseAt, List.mem_cons] at hh'
    rcases hh' with rfl | hh'
    · exact H _ List.mem_cons_self
    · exact epochsLe_releaseAt hs i (fun h'' hh'' => H h'' (List.mem_cons_of_mem _ hh'')) h' hh'

theorem epochsLe_free {t : State V S} (ht : EpochsLe t) : EpochsLe (free t) := by
  unfold free
  split
  · exact fun h hh => Nat.le_succ_of_le (ht h hh)
  · exact ht

theorem epochsLe_beginRun (interned : Bool) {t : State V S} (ht : EpochsLe t) :
    EpochsLe (beginRun interned t) := by
  unfold beginRun
  split
  · exact ht
  · exact ht

theorem epochsLe_step (interned : Bool) {st : State V S} (hs : EpochsLe st) (op : Op V S) :
    EpochsLe (step interned st op) := by
  cases op with
  | hold x s =>
    have hb := epochsLe_beginRun interned hs
    intro h hh
    simp only [step, push, List.mem_append, List.mem_singleton] at hh ⊢
    rcases hh with hh | rfl
    · exact hb h hh
    · exact Nat.le_refl _
  | release j =>
    simp only [step]
    split
    · exact epochsLe_releaseAt st.held j hs
    · exact hs
  | reset =>
    have hk : EpochsLe { st with held := killAll st.held } := by
      intro h hh
      simp only [killAll, List.mem_map] at hh
      obtain ⟨h₀, hh₀, rfl⟩ := hh
      exact hs h₀ hh₀
    simp only [step]
    split
    · exact epochsLe_free hk
    · exact hk
  | call big =>
    simp only [step]
    split
    · exact epochsLe_free (epochsLe_beginRun interned hs)
    · exact epochsLe_beginRun interned hs
  | stop =>
    simp only [step]
    split
    · exact epochsLe_free (epochsLe_beginRun interned hs)
    · exact hs

/-- A refused issued handle stays refused after one operation. -/
theorem dead_step (interned : Bool) {st : State V S} (hs : EpochsLe st) {i : Nat}
    (hd : Dead st i) (op : Op V S) : Dead (step interned st op) i := by
  obtain ⟨h, e, hv⟩ := dead_iff.mp hd
  obtain ⟨h', e', -, -, hep, hlive⟩ := entry_step interned st op e
  have hle : h.epoch ≤ st.epoch := hs h (List.mem_of_getElem? e)
  have hmono := epoch_le_step interned st op
  refine dead_iff.mpr ⟨h', e', fun ⟨hl, he⟩ => hv ⟨hlive hl, ?_⟩⟩
  omega

/-- The epoch invariant holds after every run of operations from the start. -/
theorem epochsLe_run (interned : Bool) : ∀ {st : State V S} (ops : List (Op V S)),
    EpochsLe st → EpochsLe (run interned st ops)
  | _, [], hs => hs
  | _, op :: ops, hs => epochsLe_run interned ops (epochsLe_step interned hs op)

/-- **A refused issued handle stays refused** through every later run of operations: released, or
of an older store, it never answers again. -/
theorem dead_run (interned : Bool) : ∀ {st : State V S} (ops : List (Op V S)) {i : Nat},
    EpochsLe st → Dead st i → Dead (run interned st ops) i
  | _, [], _, _, hd => hd
  | _, op :: ops, _, hs, hd =>
    dead_run interned ops (epochsLe_step interned hs op) (dead_step interned hs hd op)

/-! ## Resets and stopped runs -/

/-- **After a reset every handle is refused**, whether or not the module has interned sorts:
`OPS reset` marks every entry not live before it frees the store. -/
theorem reset_refuses (interned : Bool) (st : State V S) (i : Nat) :
    lookup (step interned st .reset) i = none := by
  have hk : ∀ t : State V S, t.held = killAll st.held → lookup t i = none := by
    intro t ht
    unfold lookup
    rw [ht]
    simp only [killAll, List.getElem?_map]
    cases st.held[i]? with
    | none => rfl
    | some h => simp
  simp only [step]
  split
  · exact hk _ (by unfold free; split <;> rfl)
  · exact hk _ rfl

/-- **Every handle issued before a reset is refused after it**, and it stays refused
(`dead_run`). -/
theorem reset_dead (interned : Bool) (st : State V S) {i : Nat} (hi : i < st.held.length) :
    Dead (step interned st .reset) i :=
  ⟨Nat.lt_of_lt_of_le hi (length_step interned st .reset), reset_refuses interned st i⟩

/-- After `rc_intern_free` of an active store no handle answers. -/
theorem free_none_valid {t : State V S} (ht : EpochsLe t) (ha : t.active = true) :
    ¬ anyValid (free t) := by
  rintro ⟨h, hh, _, he⟩
  unfold free at hh he
  rw [if_pos ha] at hh he
  have := ht h hh
  simp only at he
  omega

/-- **After a call stopped by a refinement violation** of a module with interned sorts every handle
is refused: the store is freed. -/
theorem stop_refuses {st : State V S} (hs : EpochsLe st) (i : Nat) :
    lookup (step true st .stop) i = none := by
  cases e : lookup (step true st .stop) i with
  | none => rfl
  | some p =>
    obtain ⟨x, s⟩ := p
    obtain ⟨h, eh, hv, -, -⟩ := lookup_eq_some_iff.mp e
    exact absurd ⟨h, List.mem_of_getElem? eh, hv⟩ (free_none_valid (epochsLe_beginRun true hs) rfl)

/-- A module without interned sorts frees no store when a call stops, and its handles keep their
values. -/
theorem stop_without_interned (st : State V S) : step false st .stop = st := rfl

/-! ## Ids are never reused, and an old handle never answers a newer value -/

theorem run_append (interned : Bool) : ∀ (st : State V S) (ops : List (Op V S)) (op : Op V S),
    run interned st (ops ++ [op]) = step interned (run interned st ops) op
  | _, [], _ => rfl
  | st, o :: ops, op => run_append interned (step interned st o) ops op

theorem length_run (interned : Bool) : ∀ (st : State V S) (ops : List (Op V S)),
    st.held.length ≤ (run interned st ops).held.length
  | _, [] => Nat.le_refl _
  | st, op :: ops => Nat.le_trans (length_step interned st op) (length_run interned _ ops)

theorem length_hold (interned : Bool) (st : State V S) (x : V) (s : S) :
    (step interned st (.hold x s)).held.length = st.held.length + 1 := by
  have hb : (beginRun interned st).held = st.held := by unfold beginRun; split <;> rfl
  simp only [step, push, hb, List.length_append, List.length_singleton]

/-- **Ids are never reused**: after a hold, every later hold answers a larger id. -/
theorem later_hold_id (interned : Bool) (st : State V S) (x : V) (s : S) (ops : List (Op V S)) :
    holdId st < holdId (run interned (step interned st (.hold x s)) ops) := by
  have := length_run interned (step interned st (.hold x s)) ops
  rw [length_hold] at this
  unfold holdId
  omega

theorem entry_run (interned : Bool) : ∀ (st : State V S) (ops : List (Op V S)) {i : Nat}
    {h : Held V S}, st.held[i]? = some h →
    ∃ h', (run interned st ops).held[i]? = some h' ∧ h'.value = h.value ∧ h'.sort = h.sort
  | _, [], _, h, e => ⟨h, e, rfl, rfl⟩
  | st, op :: ops, _, _, e => by
    obtain ⟨h₁, e₁, hv₁, hs₁, -, -⟩ := entry_step interned st op e
    obtain ⟨h₂, e₂, hv₂, hs₂⟩ := entry_run interned _ ops e₁
    exact ⟨h₂, e₂, hv₂.trans hv₁, hs₂.trans hs₁⟩

/-- **An old handle answers its own value or nothing** after every later run of operations. -/
theorem old_handle_answers_own (interned : Bool) {st : State V S} {i : Nat} {h : Held V S}
    (e : st.held[i]? = some h) (ops : List (Op V S)) :
    lookup (run interned st ops) i = none ∨ lookup (run interned st ops) i = some (h.value, h.sort) := by
  cases el : lookup (run interned st ops) i with
  | none => exact Or.inl rfl
  | some p =>
    obtain ⟨x, s⟩ := p
    obtain ⟨h', e', -, hx, hs⟩ := lookup_eq_some_iff.mp el
    obtain ⟨h'', e'', hv, hs'⟩ := entry_run interned st ops e
    rw [e'] at e''
    cases e''
    exact Or.inr (by rw [← hx, ← hs, hv, hs'])

/-- **A value held later gets a new handle, and the old handle never answers it**: after holding
`x`, any run of operations, then holding `y`, the new handle answers `y`, and the old one answers
`x` or nothing, never `y` unless `y = x`. -/
theorem old_handle_not_newer (interned : Bool) (st : State V S) (x y : V) (s s' : S)
    (ops : List (Op V S)) :
    let st₁ := step interned st (.hold x s)
    let st₂ := run interned st₁ ops
    holdId st ≠ holdId st₂ ∧ lookup (step interned st₂ (.hold y s')) (holdId st₂) = some (y, s') ∧
      ∀ z, lookup (step interned st₂ (.hold y s')) (holdId st) = some z → z = (x, s) := by
  intro st₁ st₂
  have hb : (beginRun interned st).held = st.held := by unfold beginRun; split <;> rfl
  have e : st₁.held[holdId st]? = some ⟨x, s, (beginRun interned st).epoch, true⟩ := by
    simp only [st₁, step, push, holdId, hb]
    rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
    rfl
  refine ⟨Nat.ne_of_lt (later_hold_id interned st x s ops), hold_answers interned st₂ y s', ?_⟩
  intro z hz
  have key := old_handle_answers_own interned e (ops ++ [.hold y s'])
  rw [run_append, hz] at key
  rcases key with key | key
  · exact absurd key nofun
  · exact Option.some.inj key

/-! ## Examples -/

section Examples

theorem hold_answers_init (interned : Bool) (x : V) (s : S) :
    lookup (step interned State.init (.hold x s)) 0 = some (x, s) :=
  hold_answers interned State.init x s

example : lookup (run true State.init [.hold 7 true]) 0 = some (7, true) :=
  hold_answers_init true 7 true

/-- The second hold answers id `1`, a new handle; the released first one is refused, the second
answers its value. -/
example : holdId (run true State.init [.hold (V := Nat) 7 true]) = 1 := rfl
example : lookup (run true State.init [.hold 7 true, .hold 8 false, .release 0]) 0 = none := by
  rw [show [Op.hold 7 true, .hold 8 false, .release 0] = [.hold 7 true, .hold 8 false] ++ [.release 0]
    from rfl, run_append]
  exact release_refuses true _ 0
example : lookup (run true State.init [.hold 7 true, .hold 8 false]) 1 = some (8, false) := by
  rw [show [Op.hold 7 true, .hold 8 false] = [.hold 7 true] ++ [.hold 8 false] from rfl, run_append]
  exact hold_answers true _ 8 false

/-- A reset refuses the handle that answered before it, with or without interned sorts. -/
example (interned : Bool) : lookup (run interned State.init [.hold 7 true]) 0 = some (7, true) ∧
    lookup (run interned State.init [.hold 7 true, .reset]) 0 = none := by
  refine ⟨hold_answers_init interned 7 true, ?_⟩
  rw [show [Op.hold 7 true, .reset] = [.hold 7 true] ++ [.reset] from rfl, run_append]
  exact reset_refuses interned _ 0

/-- A stopped call refuses the handle that answered before it (a module with interned sorts). -/
example : lookup (run true State.init [.hold 7 true, .stop]) 0 = none := by
  rw [show [Op.hold 7 true, .stop] = [.hold 7 true] ++ [.stop] from rfl, run_append]
  exact stop_refuses (epochsLe_step true epochsLe_init _) 0

/-- A never-issued id is refused. -/
example : lookup (run true State.init [.hold 7 true]) 5 = none := lookup_out_of_range (by decide)

/-- A handle is read with the sort expected. -/
example : lookupSort (run true State.init [.hold 7 true]) 0 true = some 7 := by
  simp only [run, lookupSort, hold_answers_init, if_pos]
example : lookupSort (run true State.init [.hold 7 true]) 0 false = none := by
  simp only [run, lookupSort, hold_answers_init]
  rfl

/-- A refused issued handle exists, so `dead_run` is not vacuous. -/
example : Dead (run true State.init [.hold 7 true, .hold 8 false, .release 0]) 0 := by
  rw [show [Op.hold 7 true, .hold 8 false, .release 0] = [.hold 7 true, .hold 8 false] ++ [.release 0]
    from rfl, run_append]
  exact ⟨by decide, release_refuses true _ 0⟩

end Examples

end Mettapedia.Languages.HOLLight.RuleModuleHandles

/-! ## Axioms -/

#print axioms Mettapedia.Languages.HOLLight.RuleModuleHandles.lookup_eq_some_iff
#print axioms Mettapedia.Languages.HOLLight.RuleModuleHandles.lookup_out_of_range
#print axioms Mettapedia.Languages.HOLLight.RuleModuleHandles.length_releaseAt
#print axioms Mettapedia.Languages.HOLLight.RuleModuleHandles.getElem?_releaseAt
#print axioms Mettapedia.Languages.HOLLight.RuleModuleHandles.hold_answers
#print axioms Mettapedia.Languages.HOLLight.RuleModuleHandles.hold_answers_sort
#print axioms Mettapedia.Languages.HOLLight.RuleModuleHandles.release_refuses
#print axioms Mettapedia.Languages.HOLLight.RuleModuleHandles.dead_iff
#print axioms Mettapedia.Languages.HOLLight.RuleModuleHandles.epoch_le_step
#print axioms Mettapedia.Languages.HOLLight.RuleModuleHandles.entry_step
#print axioms Mettapedia.Languages.HOLLight.RuleModuleHandles.length_step
#print axioms Mettapedia.Languages.HOLLight.RuleModuleHandles.epochsLe_init
#print axioms Mettapedia.Languages.HOLLight.RuleModuleHandles.epochsLe_releaseAt
#print axioms Mettapedia.Languages.HOLLight.RuleModuleHandles.epochsLe_free
#print axioms Mettapedia.Languages.HOLLight.RuleModuleHandles.epochsLe_beginRun
#print axioms Mettapedia.Languages.HOLLight.RuleModuleHandles.epochsLe_step
#print axioms Mettapedia.Languages.HOLLight.RuleModuleHandles.dead_step
#print axioms Mettapedia.Languages.HOLLight.RuleModuleHandles.epochsLe_run
#print axioms Mettapedia.Languages.HOLLight.RuleModuleHandles.dead_run
#print axioms Mettapedia.Languages.HOLLight.RuleModuleHandles.reset_refuses
#print axioms Mettapedia.Languages.HOLLight.RuleModuleHandles.reset_dead
#print axioms Mettapedia.Languages.HOLLight.RuleModuleHandles.free_none_valid
#print axioms Mettapedia.Languages.HOLLight.RuleModuleHandles.stop_refuses
#print axioms Mettapedia.Languages.HOLLight.RuleModuleHandles.stop_without_interned
#print axioms Mettapedia.Languages.HOLLight.RuleModuleHandles.run_append
#print axioms Mettapedia.Languages.HOLLight.RuleModuleHandles.length_run
#print axioms Mettapedia.Languages.HOLLight.RuleModuleHandles.length_hold
#print axioms Mettapedia.Languages.HOLLight.RuleModuleHandles.later_hold_id
#print axioms Mettapedia.Languages.HOLLight.RuleModuleHandles.entry_run
#print axioms Mettapedia.Languages.HOLLight.RuleModuleHandles.old_handle_answers_own
#print axioms Mettapedia.Languages.HOLLight.RuleModuleHandles.old_handle_not_newer
#print axioms Mettapedia.Languages.HOLLight.RuleModuleHandles.hold_answers_init

-- Written by a sub-agent of Claude (Oruži), main:14 "CC FM".
