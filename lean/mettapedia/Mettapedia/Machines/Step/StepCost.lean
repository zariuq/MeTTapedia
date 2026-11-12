import Mettapedia.Machines.Step.ResidualReader
import Mettapedia.Machines.Step.Firing

/-!
# What the step costs beside `match`

The store is the stamped ordered index of `ResidualReader`.  A pattern is a
decidable property of keys.  Three things are counted (`Cost`): searches of the
index (each returns at most one row, so row visits are at most the searches),
validations (one comparison of a row's death stamp), and writes (one stamp
written).

`match` is a reader that passes the keys that are not candidates
(`matchPull`).  The step makes one *attempt* per pull (`attempt`): the same
search for the next candidate of the entry view, and then, by mode,

* `read`: deliver the candidate;
* `recheck`: one validation, and deliver if the row is live now;
* `take`: one validation, and if the row is live now one write that stamps its
  death, and deliver.

Results:

* `attempt_read_eq_match`: in mode `read` an attempt is `match`'s pull: the
  same answer, the same reader after, the same searches, no validation and no
  write, and the index untouched.  Reads alone cost what `match` costs; the
  only addition per call is reading the clock once to open the reader, which
  `match`'s lawful cursor does as well.
* `attempt_recheck_cost`: rechecking a read adds exactly one validation per
  candidate and nothing else.
* `attempt_take_fired`, `take_is_a_firing`: a fired take found a row that is
  live now, is a firing of the store's present content in the sense of
  `Firing`, and costs the search plus one validation and one write.  By
  `LowerBounds.validation_cost` and `LowerBounds.writes_lower_bound` no
  correct implementation spends fewer validations or writes per take.
* `take_saves_a_search`: where a program takes by `match` followed by a
  removal by key, the removal searches the index again; the step's take costs
  exactly one search less per taken row, and reaches the same index.
* `takeRun_nodup`, `Controls.match_then_remove_delivers_twice`: over any
  sequence of take attempts by any readers no row is delivered twice; two
  consumers that each match and then remove can both deliver the same row.
* `attempt_searches_le`, `eager_searches_ge`, `first_answer_one_search`: the
  searches before a first answer are at most the keys up to it, whatever lies
  beyond; enumerating the candidates first costs at least one search per
  candidate.  When the first key is a candidate the first answer costs one
  search and the enumeration costs more than the number of candidates.
* `keyAbsent_iff`: an `absent` condition on a key is decided now by one search
  and one validation, without enumerating anything.

Positive and negative examples: `Controls`.

Not modelled: what a search costs in the index it stands for, the cost of
calling the operation at all, patterns that are not properties of one key
(conjunctions are the seekers of `SeekerJoin`, read through the same
attempts), and a removal that finds its rows by scanning, which costs the
stored rows instead of one search.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Step.StepCost

open Index

/-- What is counted. -/
structure Cost where
  searches : ℕ
  validations : ℕ
  writes : ℕ
  deriving DecidableEq, Repr

instance : Add Cost :=
  ⟨fun a b => ⟨a.searches + b.searches, a.validations + b.validations, a.writes + b.writes⟩⟩

theorem Cost.add_def (a b : Cost) :
    a + b = ⟨a.searches + b.searches, a.validations + b.validations, a.writes + b.writes⟩ := rfl

variable {K : Type*} [LinearOrder K]

/-- A candidate of a pattern for a reader: visible at its time, and matching. -/
def Candidate (idx : Index K) (t : ℕ) (p : K → Prop) (k : K) : Prop := idx.Visible t k ∧ p k

instance (idx : Index K) (t : ℕ) (p : K → Prop) [DecidablePred p] :
    DecidablePred (Candidate idx t p) := fun k => by
  unfold Candidate
  infer_instance

/-- The index as it is held. -/
abbrev phys (idx : Index K) : Seeker K := Seeker.ofFinset idx.held

/-- The row is live now: held, with no death stamp.  One comparison. -/
def LiveNow (idx : Index K) (k : K) : Prop := k ∈ idx.held ∧ idx.died k = none

instance (idx : Index K) : DecidablePred (LiveNow idx) := fun k => by
  unfold LiveNow
  infer_instance

/-- One pull of `match`'s cursor: the next candidate, the reader past it, and
the searches made. -/
def matchPull (p : K → Prop) [DecidablePred p] (rd : Reader K) (idx : Index K) :
    Option K × Reader K × Cost :=
  match (phys idx).filterSeek (Candidate idx rd.time p) rd.bound with
  | none => (none, rd, ⟨(phys idx).filterSeeks (Candidate idx rd.time p) rd.bound, 0, 0⟩)
  | some k =>
    (some k, { rd with bound := .gt k },
      ⟨(phys idx).filterSeeks (Candidate idx rd.time p) rd.bound, 0, 0⟩)

/-- What a branch does with the candidate it found. -/
inductive Mode where
  | read
  | recheck
  | take
  deriving DecidableEq

/-- How an attempt ends. -/
inductive Outcome (K : Type*) where
  | exhausted
  | refused (k : K)
  | fired (k : K)
  deriving DecidableEq

/-- One attempt of the step: search the next candidate of the entry view, then
validate and commit by mode. -/
def attempt (mode : Mode) (p : K → Prop) [DecidablePred p] (rd : Reader K) (idx : Index K) :
    Outcome K × Reader K × Index K × Cost :=
  match (phys idx).filterSeek (Candidate idx rd.time p) rd.bound with
  | none =>
    (.exhausted, rd, idx, ⟨(phys idx).filterSeeks (Candidate idx rd.time p) rd.bound, 0, 0⟩)
  | some k =>
    match mode with
    | .read =>
      (.fired k, { rd with bound := .gt k }, idx,
        ⟨(phys idx).filterSeeks (Candidate idx rd.time p) rd.bound, 0, 0⟩)
    | .recheck =>
      (if LiveNow idx k then .fired k else .refused k, { rd with bound := .gt k }, idx,
        ⟨(phys idx).filterSeeks (Candidate idx rd.time p) rd.bound, 1, 0⟩)
    | .take =>
      if LiveNow idx k then
        (.fired k, { rd with bound := .gt k }, apply (.kill k) idx,
          ⟨(phys idx).filterSeeks (Candidate idx rd.time p) rd.bound, 1, 1⟩)
      else
        (.refused k, { rd with bound := .gt k }, idx,
          ⟨(phys idx).filterSeeks (Candidate idx rd.time p) rd.bound, 1, 0⟩)

/-- **Reads alone cost what `match` costs.**  In mode `read` an attempt is
`match`'s pull, answer for answer and search for search; it validates nothing,
writes nothing and leaves the index as it is. -/
theorem attempt_read_eq_match (p : K → Prop) [DecidablePred p] (rd : Reader K) (idx : Index K) :
    attempt .read p rd idx =
      (match (matchPull p rd idx).1 with
        | none => .exhausted
        | some k => .fired k,
       (matchPull p rd idx).2.1, idx, (matchPull p rd idx).2.2) := by
  unfold attempt matchPull
  cases (phys idx).filterSeek (Candidate idx rd.time p) rd.bound <;> rfl

/-- **Rechecking a read costs one validation per candidate**, and nothing
else: the same reader after, the same index, the same searches. -/
theorem attempt_recheck_cost (p : K → Prop) [DecidablePred p] (rd : Reader K) (idx : Index K)
    (k : K) (found : (matchPull p rd idx).1 = some k) :
    (attempt .recheck p rd idx).2.1 = (matchPull p rd idx).2.1 ∧
      (attempt .recheck p rd idx).2.2.1 = idx ∧
      (attempt .recheck p rd idx).2.2.2 = (matchPull p rd idx).2.2 + ⟨0, 1, 0⟩ ∧
      ((attempt .recheck p rd idx).1 = .fired k ↔ LiveNow idx k) := by
  unfold attempt matchPull at *
  cases h : (phys idx).filterSeek (Candidate idx rd.time p) rd.bound with
  | none => rw [h] at found; cases found
  | some k' =>
    rw [h] at found
    cases found
    refine ⟨rfl, rfl, rfl, ?_⟩
    by_cases live : LiveNow idx k
    · simp [live]
    · simp [live]

/-- What a fired take is: its row was a candidate of the entry view the bound
admitted, it is live now, the index after is the index with that row's death
stamped, and the cost is the search, one validation and one write. -/
theorem attempt_take_fired (p : K → Prop) [DecidablePred p] (rd : Reader K) (idx : Index K)
    (k : K) (fired : (attempt .take p rd idx).1 = .fired k) :
    (matchPull p rd idx).1 = some k ∧ LiveNow idx k ∧
      attempt .take p rd idx =
        (.fired k, (matchPull p rd idx).2.1, apply (.kill k) idx,
          (matchPull p rd idx).2.2 + ⟨0, 1, 1⟩) := by
  unfold attempt matchPull at *
  cases h : (phys idx).filterSeek (Candidate idx rd.time p) rd.bound with
  | none => rw [h] at fired; cases fired
  | some k' =>
    rw [h] at fired
    by_cases live : LiveNow idx k'
    · simp only [live, if_true] at fired
      cases fired
      exact ⟨rfl, live, by simp [live, Cost.add_def]⟩
    · simp only [live, if_false] at fired
      cases fired

/-- The outcome of a take once its candidate is known: fired if the row is
live now, refused otherwise. -/
theorem attempt_take_outcome (p : K → Prop) [DecidablePred p] (rd : Reader K) (idx : Index K)
    (k : K) (found : (phys idx).filterSeek (Candidate idx rd.time p) rd.bound = some k) :
    (attempt .take p rd idx).1 = if LiveNow idx k then .fired k else .refused k := by
  unfold attempt
  rw [found]
  by_cases live : LiveNow idx k <;> simp [live]

/-- A take that is refused or finds nothing leaves the index as it is. -/
theorem attempt_take_not_fired (p : K → Prop) [DecidablePred p] (rd : Reader K) (idx : Index K)
    (not : ∀ k, (attempt .take p rd idx).1 ≠ .fired k) : (attempt .take p rd idx).2.2.1 = idx := by
  unfold attempt at *
  cases h : (phys idx).filterSeek (Candidate idx rd.time p) rd.bound with
  | none => rfl
  | some k' =>
    rw [h] at not
    by_cases live : LiveNow idx k'
    · exact absurd (by simp [live]) (not k')
    · simp [live]

/-- After its death is stamped a row is not live, and every other row is as it
was. -/
theorem liveNow_kill (idx : Index K) (k k' : K) (live : LiveNow idx k) :
    LiveNow (apply (.kill k) idx) k' ↔ LiveNow idx k' ∧ k' ≠ k := by
  rw [apply_kill, if_pos (show k ∈ idx.held ∧ idx.died k = none from live)]
  unfold LiveNow
  by_cases eq : k' = k
  · subst eq
    simp
  · simp [eq]

/-- The store's present content: its live rows. -/
def content (idx : Index K) : Multiset K := (idx.held.filter (LiveNow idx)).val

/-- The firing that takes one row and delivers nothing to the store. -/
def takeFiring (k : K) : Firing K := ⟨0, {k}, fun _ => False, 0⟩

/-- **A fired take is a firing of the store as it is**: enabled on the present
content, and the content after is the content without the row. -/
theorem take_is_a_firing (idx : Index K) (k : K) (live : LiveNow idx k) :
    (takeFiring k).Enabled (content idx) ∧
      (takeFiring k).fire (content idx) = content (apply (.kill k) idx) := by
  have mem : k ∈ content idx := Finset.mem_filter.mpr ⟨live.1, live⟩
  refine ⟨⟨Multiset.singleton_le.mpr mem, fun _ h => by simp [takeFiring] at h, fun _ _ h => h⟩, ?_⟩
  have after : (apply (.kill k) idx).held.filter (LiveNow (apply (.kill k) idx)) =
      (idx.held.filter (LiveNow idx)).erase k := by
    ext x
    rw [Finset.mem_filter, Finset.mem_erase, Finset.mem_filter, liveNow_kill idx k x live]
    have held : (apply (.kill k) idx).held = idx.held := by
      rw [apply_kill, if_pos (show k ∈ idx.held ∧ idx.died k = none from live)]
    rw [held]
    tauto
  simp only [content, Firing.fire, takeFiring, after, Finset.erase_val, Multiset.sub_singleton,
    add_zero]

/-- A sequence of take attempts, by any readers in any order: the rows
delivered, and the index after. -/
def takeRun (p : K → Prop) [DecidablePred p] : List (Reader K) → Index K → List K × Index K
  | [], idx => ([], idx)
  | rd :: rest, idx =>
    match (attempt .take p rd idx).1 with
    | .fired k =>
      let out := takeRun p rest (attempt .take p rd idx).2.2.1
      (k :: out.1, out.2)
    | _ => takeRun p rest (attempt .take p rd idx).2.2.1

theorem takeRun_live (p : K → Prop) [DecidablePred p] (rds : List (Reader K)) (idx : Index K) :
    ∀ k ∈ (takeRun p rds idx).1, LiveNow idx k := by
  induction rds generalizing idx with
  | nil => exact fun k h => by simp [takeRun] at h
  | cons rd rest ih =>
    intro k hk
    unfold takeRun at hk
    cases out : (attempt .take p rd idx).1 with
    | fired k' =>
      obtain ⟨_, live, eq⟩ := attempt_take_fired p rd idx k' out
      rw [out] at hk
      simp only [List.mem_cons] at hk
      rcases hk with rfl | hk
      · exact live
      · have := ih _ k hk
        rw [eq] at this
        exact ((liveNow_kill idx k' k live).mp this).1
    | exhausted =>
      rw [out] at hk
      have same := attempt_take_not_fired p rd idx (fun k h => by rw [out] at h; cases h)
      rw [same] at hk
      exact ih idx k hk
    | refused k' =>
      rw [out] at hk
      have same := attempt_take_not_fired p rd idx (fun k h => by rw [out] at h; cases h)
      rw [same] at hk
      exact ih idx k hk

/-- **No row is taken twice**, whatever readers attempt and in whatever order. -/
theorem takeRun_nodup (p : K → Prop) [DecidablePred p] (rds : List (Reader K)) (idx : Index K) :
    (takeRun p rds idx).1.Nodup := by
  induction rds generalizing idx with
  | nil => simp [takeRun]
  | cons rd rest ih =>
    unfold takeRun
    cases out : (attempt .take p rd idx).1 with
    | fired k =>
      obtain ⟨_, live, eq⟩ := attempt_take_fired p rd idx k out
      simp only [List.nodup_cons]
      refine ⟨fun again => ?_, ih _⟩
      have := takeRun_live p rest _ k again
      rw [eq] at this
      exact ((liveNow_kill idx k k live).mp this).2 rfl
    | exhausted => exact ih _
    | refused k => exact ih _

/-- A removal by key, as a program that took by `match` does it afterwards:
search the index for the key, and stamp its death if it is live. -/
def removeKey (k : K) (idx : Index K) : Bool × Index K × Cost :=
  match (phys idx).seek (.ge k) with
  | none => (false, idx, ⟨1, 0, 0⟩)
  | some k' =>
    if k' = k ∧ LiveNow idx k then (true, apply (.kill k) idx, ⟨1, 1, 1⟩)
    else (false, idx, ⟨1, 1, 0⟩)

/-- `match`, then a removal of the row it answered. -/
def matchThenRemove (p : K → Prop) [DecidablePred p] (rd : Reader K) (idx : Index K) :
    Option K × Reader K × Index K × Cost :=
  match (matchPull p rd idx).1 with
  | none => (none, (matchPull p rd idx).2.1, idx, (matchPull p rd idx).2.2)
  | some k =>
    (some k, (matchPull p rd idx).2.1, (removeKey k idx).2.1,
      (matchPull p rd idx).2.2 + (removeKey k idx).2.2)

theorem seek_held (idx : Index K) (k : K) (held : k ∈ idx.held) :
    (phys idx).seek (.ge k) = some k := by
  cases h : (phys idx).seek (.ge k) with
  | none => exact absurd (le_refl k) ((phys idx).seek_none _ h k held)
  | some k' =>
    have s := (phys idx).seek_some _ k' h
    exact congrArg some (le_antisymm (s.2.2 k held (le_refl k)) s.2.1)

/-- **The step's take saves one search per taken row.**  Whenever a take
fires, `match` followed by the removal of its answer delivers the same row and
leaves the same reader and the same index, and costs exactly one search more. -/
theorem take_saves_a_search (p : K → Prop) [DecidablePred p] (rd : Reader K) (idx : Index K)
    (k : K) (fired : (attempt .take p rd idx).1 = .fired k) :
    matchThenRemove p rd idx =
      (some k, (attempt .take p rd idx).2.1, (attempt .take p rd idx).2.2.1,
        (attempt .take p rd idx).2.2.2 + ⟨1, 0, 0⟩) := by
  obtain ⟨found, live, eq⟩ := attempt_take_fired p rd idx k fired
  have removal : removeKey k idx = (true, apply (.kill k) idx, ⟨1, 1, 1⟩) := by
    unfold removeKey
    rw [seek_held idx k live.1]
    simp [live]
  unfold matchThenRemove
  simp only [found, eq, removal]
  refine Prod.ext rfl (Prod.ext rfl (Prod.ext rfl ?_))
  simp only [Cost.add_def]

/-! ## The first answer -/

theorem filterSeeks_pos (X : Seeker K) (p : K → Prop) [DecidablePred p] (b : Bound K) :
    1 ≤ X.filterSeeks p b := by
  cases h : X.seek b with
  | none => rw [Seeker.filterSeeks_of_none X p h]
  | some k =>
    rw [Seeker.filterSeeks_of_some X p h]
    split <;> omega

/-- **The searches before an answer are at most the keys up to it.**  What the
index holds past the candidate found does not enter. -/
theorem attempt_searches_le (mode : Mode) (p : K → Prop) [DecidablePred p] (rd : Reader K)
    (idx : Index K) (k : K) (found : (matchPull p rd idx).1 = some k) :
    (attempt mode p rd idx).2.2.2.searches + (idx.held.filter (Bound.gt k).admits).card ≤
      (idx.held.filter rd.bound.admits).card := by
  unfold matchPull at found
  cases h : (phys idx).filterSeek (Candidate idx rd.time p) rd.bound with
  | none => rw [h] at found; cases found
  | some k' =>
    rw [h] at found
    cases found
    have account := ((phys idx).filterSeeks_account (Candidate idx rd.time p) rd.bound).2 k h
    unfold attempt
    rw [h]
    cases mode with
    | read => exact account
    | recheck => exact account
    | take =>
      by_cases live : LiveNow idx k
      · simp only [live, if_true]
        exact account
      · simp only [live, if_false]
        exact account

/-- **Enumerating the candidates first costs at least one search for each.** -/
theorem eager_searches_ge (X : Seeker K) (p : K → Prop) [DecidablePred p] (b : Bound K) :
    ((X.filter p).drain b).length + 1 ≤ X.filterDrainSeeks p b := by
  induction b using Seeker.bound_induction (X.filter p) with
  | step b ih =>
    rw [Seeker.filterDrainSeeks]
    split
    · rename_i h
      rw [Seeker.drain_of_none (X.filter p) h]
      exact filterSeeks_pos X p b
    · rename_i z h
      rw [Seeker.drain_of_some (X.filter p) h, List.length_cons]
      have := ih z h
      have := filterSeeks_pos X p b
      omega

/-- When the first key the bound admits is a candidate, the first answer costs
one search, however many candidates follow. -/
theorem first_answer_one_search (mode : Mode) (p : K → Prop) [DecidablePred p] (rd : Reader K)
    (idx : Index K) (k : K) (first : (phys idx).seek rd.bound = some k)
    (candidate : Candidate idx rd.time p k) :
    (attempt mode p rd idx).2.2.2.searches = 1 := by
  have seek : (phys idx).filterSeek (Candidate idx rd.time p) rd.bound = some k := by
    rw [Seeker.filterSeek_of_some _ _ first, if_pos candidate]
  have seeks : (phys idx).filterSeeks (Candidate idx rd.time p) rd.bound = 1 := by
    rw [Seeker.filterSeeks_of_some _ _ first, if_pos candidate]
  unfold attempt
  rw [seek]
  cases mode with
  | read => exact seeks
  | recheck => exact seeks
  | take =>
    by_cases live : LiveNow idx k
    · simp only [live, if_true]
      exact seeks
    · simp only [live, if_false]
      exact seeks

/-- An `absent` condition on one key, decided now: one search and one
validation. -/
def keyAbsent (idx : Index K) (c : K) : Bool × Cost :=
  match (phys idx).seek (.ge c) with
  | none => (true, ⟨1, 0, 0⟩)
  | some k => (!decide (k = c ∧ LiveNow idx c), ⟨1, 1, 0⟩)

/-- **Absence of a key is decided without enumerating.** -/
theorem keyAbsent_iff (idx : Index K) (c : K) : (keyAbsent idx c).1 = true ↔ ¬ LiveNow idx c := by
  unfold keyAbsent
  cases h : (phys idx).seek (.ge c) with
  | none =>
    simp only [true_iff]
    exact fun live => (phys idx).seek_none _ h c live.1 (le_refl c)
  | some k =>
    by_cases held : c ∈ idx.held
    · rw [seek_held idx c held] at h
      cases h
      simp
    · have : ¬ LiveNow idx c := fun live => held live.1
      simp [this]

namespace Controls

/-- Keys `1` to `4`, all live, entered at tick `4`. -/
def four : Index Nat := run [.insert 1, .insert 2, .insert 3, .insert 4] Index.empty

def fresh : Reader Nat := ⟨.all, 4⟩

/-- The even keys. -/
def even : Nat → Prop := fun k => k % 2 = 0

instance : DecidablePred even := fun k => by
  unfold even
  infer_instance

theorem even_found : (phys four).filterSeek (Candidate four 4 even) .all = some 2 := by
  rw [Seeker.filterSeek_eq_ofFinset]
  decide

theorem even_searches : (phys four).filterSeeks (Candidate four 4 even) .all = 2 := by
  have exact := ((phys four).filterSeeks_exact (Candidate four 4 even) .all).2 2 even_found
  have all : ((phys four).keys.filter (Bound.all : Bound Nat).admits).card = 4 := by decide
  have past : ((phys four).keys.filter (Bound.gt 2).admits).card = 2 := by decide
  omega

/-- Positive: a take of an even key searches twice (it passes `1`), validates
once, writes once, and delivers `2`. -/
theorem take_example :
    attempt .take even fresh four = (.fired 2, ⟨.gt 2, 4⟩, apply (.kill 2) four, ⟨2, 1, 1⟩) := by
  have found : (phys four).filterSeek (Candidate four fresh.time even) fresh.bound = some 2 :=
    even_found
  have searches : (phys four).filterSeeks (Candidate four fresh.time even) fresh.bound = 2 :=
    even_searches
  have live : LiveNow four 2 := by decide
  unfold attempt
  rw [found, searches]
  simp only [live, if_true]
  rfl

/-- Positive: the same row by `match` and then a removal costs three searches. -/
theorem match_then_remove_example :
    (matchThenRemove even fresh four).1 = some 2 ∧
      (matchThenRemove even fresh four).2.2.2 = ⟨3, 1, 1⟩ := by
  have fired : (attempt .take even fresh four).1 = .fired 2 := by rw [take_example]
  rw [take_saves_a_search even fresh four 2 fired, take_example]
  exact ⟨rfl, rfl⟩

/-- Positive: the first answer of a pattern every key matches costs one search;
enumerating its four candidates first costs at least five. -/
theorem first_answer_example :
    (attempt .read (fun _ => True) fresh four).2.2.2.searches = 1 ∧
      5 ≤ (phys four).filterDrainSeeks (Candidate four 4 fun _ => True) .all := by
  refine ⟨first_answer_one_search .read _ fresh four 1 (by decide) (by decide), ?_⟩
  have eager := eager_searches_ge (phys four) (Candidate four 4 fun _ => True) .all
  rw [Seeker.drain_length] at eager
  have card : (((phys four).filter (Candidate four 4 fun _ => True)).keys.filter
      (Bound.all : Bound Nat).admits).card = 4 := by decide
  omega

/-- Negative: two consumers that each match and then remove both match the key
`1` before either removes it; the first removal succeeds and the second finds
nothing, after its answer was delivered.  `takeRun_nodup` excludes this for
takes. -/
theorem match_then_remove_delivers_twice :
    (matchPull (fun _ => True) fresh four).1 = some 1 ∧
      (removeKey 1 four).1 = true ∧ (removeKey 1 (removeKey 1 four).2.1).1 = false := by
  refine ⟨?_, by decide, by decide⟩
  have found : (phys four).filterSeek (Candidate four fresh.time fun _ => True) fresh.bound =
      some 1 := by
    rw [Seeker.filterSeek_eq_ofFinset]
    decide
  unfold matchPull
  rw [found]

/-- Negative: a take that skipped its validation would deliver a row that is
dead now.  The entry view of time `4` still holds `1` after it is removed, so
`match` answers it, and the take refuses it. -/
theorem take_refuses_a_dead_row :
    (matchPull (fun k => k = 1) fresh (apply (.kill 1) four)).1 = some 1 ∧
      (attempt .take (fun k => k = 1) fresh (apply (.kill 1) four)).1 = .refused 1 := by
  have found : (phys (apply (.kill 1) four)).filterSeek
      (Candidate (apply (.kill 1) four) fresh.time fun k => k = 1) fresh.bound = some 1 := by
    rw [Seeker.filterSeek_eq_ofFinset]
    decide
  have dead : ¬ LiveNow (apply (.kill 1) four) 1 := by decide
  constructor
  · unfold matchPull
    rw [found]
  · unfold attempt
    rw [found]
    simp only [dead, if_false]

/-- Positive and negative: the key `9` is absent and the key `3` is not, each
by one search. -/
theorem key_absent_example :
    keyAbsent four 9 = (true, ⟨1, 0, 0⟩) ∧ keyAbsent four 3 = (false, ⟨1, 1, 0⟩) := by
  decide

end Controls

end Mettapedia.Machines.Step.StepCost
