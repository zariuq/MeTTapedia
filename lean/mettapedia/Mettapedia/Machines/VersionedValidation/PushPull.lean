import Mettapedia.Machines.VersionedValidation.Granularity

/-!
# Push and pull invalidation, and their costs

Pull compares the stamp with the current counters at each use. Push inverts the
work: each retained decision subscribes to the classes of its stamp, a step that
moves the counter of a class notifies every subscriber of that class, and a
notified decision is dirty. A use reuses exactly when the decision is not dirty.

For monotone counters, in particular every versioning, push and pull make the same
reuse decision at every use (`dirty_iff_not_stampAgrees`, `push_eq_pull`), also
for a population with an explicit subscriber table
(`pushDirty_eq_not_checkStamp`). Push needs less: counters that signal every
change suffice, monotone or not (`push_sound`). A counter that wraps around breaks
pull and not push (`Controls.wrapping_counter_breaks_pull`).

## Costs: instances of `queryWork`

Every strategy is a probe schedule of the one cost model `queryWork`:
* pull (`pullWork`): an event at every use, paying the stamp length, never a miss;
* push (`pushWork`): an event at every step, paying nothing, and one notification
  exactly when a subscribed counter moved there. The subscriber table sends the
  notifications of every class to each of its subscribers (`pushNotifications_eq`);
* the hybrid check (`hybridRun`): an event at every use, paying one comparison of
  the global counter, and the stamp length when the global counter moved since the
  reference, under either policy (`hybridRun_eq_queryWork`);
* the validating strategy (`strategyWork`): an event at every use, paying the stamp
  length, and the read check at every alarm; its alarms are the refreshing misses
  of the class mark (`alarmCount_serve_eq_gaps`, `strategyWork_eq_queryWork`).

Neither push nor pull dominates (`neither_dominates`): on read-heavy histories
pull costs `m * m` and push `m` with a dirty-bit test per use; on write-heavy
histories push costs `m` and pull `1`. The refreshing hybrid never costs more
than the epoch hybrid (`hybridRun_refreshing_le_epoch`), strictly less after an
early unrelated change (`Controls.epoch_hybrid_exceeds_refreshed`). Refinement
supplies the covering hypothesis of `global_miss_gap` (`classMark_covers`), so the
alarms of a global counter are the class alarms plus the gaps in which only the
global counter moved (`global_alarms_eq`). Refreshing probes count gaps and push
counts moves (`Controls.gaps_not_moves`).
-/

set_option autoImplicit false

namespace Mettapedia.Machines.VersionedValidation

open ReadOnlyQuery
open Mettapedia.GSLT.Contracts.ReadWindowCuts (Cut Discipline)

universe u v w

/-! ## Push for one decision -/

section Dirty

variable {steps : ℕ} {K : Type w}

/-- The counter of `k` moved at step `i`. -/
def movedAt (ver : Cut steps → K → ℕ) (i : Fin steps) (k : K) : Bool :=
  decide (ver i.castSucc k ≠ ver i.succ k)

/-- Step `i` lies in the window `[t0, t]`. -/
def inWindow (t0 t : Cut steps) (i : Fin steps) : Bool :=
  decide (t0 ≤ i.castSucc) && decide (i.succ ≤ t)

/-- Push for one retained decision, subscribed at `t0` to the classes
`subscribed`: at `t` it is dirty when a step of the window `[t0, t]` moved the
counter of a subscribed class. -/
def dirty (ver : Cut steps → K → ℕ) (subscribed : List K) (t0 t : Cut steps) : Bool :=
  (List.finRange steps).any fun i => inWindow t0 t i && subscribed.any (movedAt ver i)

theorem dirty_eq_true_iff {ver : Cut steps → K → ℕ} {subscribed : List K} {t0 t : Cut steps} :
    dirty ver subscribed t0 t = true ↔
      ∃ i : Fin steps, t0 ≤ i.castSucc ∧ i.succ ≤ t ∧
        ∃ k ∈ subscribed, ver i.castSucc k ≠ ver i.succ k := by
  simp [dirty, inWindow, movedAt, and_assoc]

/-- **Push equals pull.** For monotone counters, a decision is dirty at `t`
exactly when its stamp disagrees at `t`. -/
theorem dirty_iff_not_stampAgrees {ver : Cut steps → K → ℕ}
    (mono : ∀ (i : Fin steps) k, ver i.castSucc k ≤ ver i.succ k) {t0 t : Cut steps}
    (le : t0 ≤ t) (subscribed : List K) :
    dirty ver subscribed t0 t = true ↔
      ¬ StampAgrees ver t (subscribed.map fun k => (k, ver t0 k)) := by
  rw [dirty_eq_true_iff, stampAgrees_map_iff]
  constructor
  · rintro ⟨i, lo, hi, k, member, moved⟩ agrees
    have increasing : Monotone fun cut => ver cut k :=
      Fin.monotone_iff_le_succ.mpr fun i => mono i k
    have first := increasing lo
    have last := increasing hi
    have step := mono i k
    have same := agrees k member
    simp only at first last
    omega
  · intro disagrees
    simp only [not_forall] at disagrees
    obtain ⟨k, member, differs⟩ := disagrees
    obtain ⟨i, lo, hi, moved⟩ :=
      exists_step_of_ne (f := fun cut => ver cut k) le (Ne.symm differs)
    exact ⟨i, lo, hi, k, member, moved⟩

variable [DecidableEq K]
variable {Key : Type u} {Value : Type v} {store : History steps Key Value} {cls : Key → K}
variable {ver : Cut steps → K → ℕ}

/-- Push and pull make the same reuse decision for a taken stamp, on every
history with a versioning. -/
theorem push_eq_pull (versioning : IsVersioning store cls ver) {t0 t : Cut steps}
    (le : t0 ≤ t) (reads : Reads Key Value) :
    (!dirty ver (classes cls reads) t0 t) = checkStamp ver t (takeStamp cls ver t0 reads) := by
  have same := dirty_iff_not_stampAgrees versioning.advance le (classes cls reads)
  rw [← checkStamp_iff] at same
  change _ = checkStamp ver t ((classes cls reads).map fun k => (k, ver t0 k))
  cases dirtyBit : dirty ver (classes cls reads) t0 t <;>
    cases checked : checkStamp ver t ((classes cls reads).map fun k => (k, ver t0 k)) <;>
    simp_all

/-- **Push is sound without monotonicity.** Counters that move at every change of
a key of their class suffice: a clean decision's reads still agree. -/
theorem push_sound
    (signals : ∀ (i : Fin steps) n, store i.succ n ≠ store i.castSucc n →
      ver i.castSucc (cls n) ≠ ver i.succ (cls n))
    {t0 t : Cut steps} (le : t0 ≤ t) {reads : Reads Key Value} (taken : Agrees (store t0) reads)
    (clean : dirty ver (classes cls reads) t0 t = false) : Agrees (store t) reads := by
  intro read member
  rw [← taken read member]
  apply eq_of_steps (f := fun cut => store cut read.1) le
  intro i lo hi
  by_contra changed
  have notified := dirty_eq_true_iff.mpr
    ⟨i, lo, hi, cls read.1, mem_classes.mpr ⟨read, member, rfl⟩,
      signals i read.1 (Ne.symm changed)⟩
  rw [clean] at notified
  exact Bool.false_ne_true notified

/-- Reuse of a clean decision returns the fresh run. -/
theorem push_reuse_sound {Answer : Type*}
    (signals : ∀ (i : Fin steps) n, store i.succ n ≠ store i.castSucc n →
      ver i.castSucc (cls n) ≠ ver i.succ (cls n))
    {t0 t : Cut steps} (le : t0 ≤ t) (program : Program Key Value Answer)
    (clean : dirty ver (classes cls (run (store t0) program).reads) t0 t = false) :
    run (store t) program = run (store t0) program :=
  run_eq_of_agrees _ _ program (push_sound signals le (run_agrees _ program) clean)

end Dirty

/-! ## A population with a subscriber table -/

section Population

variable {steps : ℕ} {K : Type w} [DecidableEq K]

/-- Retained decisions by position, each given by the classes it subscribes to,
which are the classes of its stamp. -/
abbrev Population (K : Type w) := List (List K)

/-- Every class some retained decision subscribes to. -/
def subscribedClasses (population : Population K) : List K :=
  population.flatten.dedup

/-- The subscriber table: the positions of the decisions subscribed to `k`. -/
def subscribers (population : Population K) (k : K) : List ℕ :=
  (List.range population.length).filter fun j => decide (k ∈ population.getD j [])

/-- The subscribed classes whose counters move at step `i`. -/
def movedClasses (ver : Cut steps → K → ℕ) (population : Population K) (i : Fin steps) :
    List K :=
  (subscribedClasses population).filter (movedAt ver i)

/-- The notifications pushed at step `i`: one per moved class and subscriber. -/
def notifications (ver : Cut steps → K → ℕ) (population : Population K) (i : Fin steps) :
    List (K × ℕ) :=
  (movedClasses ver population i).flatMap fun k => (subscribers population k).map fun j => (k, j)

/-- The dirty table of the push machine: decision `j` is dirty at `t` when it was
notified at a step of the window `[t0, t]`. -/
def pushDirty (ver : Cut steps → K → ℕ) (population : Population K) (t0 t : Cut steps)
    (j : ℕ) : Bool :=
  (List.finRange steps).any fun i =>
    inWindow t0 t i && (notifications ver population i).any fun note => note.2 == j

theorem notified_eq {ver : Cut steps → K → ℕ} {population : Population K} {j : ℕ}
    (present : j < population.length) (i : Fin steps) :
    ((notifications ver population i).any fun note => note.2 == j) =
      (population.getD j []).any (movedAt ver i) := by
  have entry : population.getD j [] ∈ population := by
    rw [List.getD_eq_getElem _ _ present]
    exact List.getElem_mem present
  apply Bool.eq_iff_iff.mpr
  simp only [notifications, movedClasses, subscribers, subscribedClasses, List.any_eq_true,
    List.mem_flatMap, List.mem_filter, List.mem_map, List.mem_range, List.mem_dedup,
    List.mem_flatten, decide_eq_true_eq, beq_iff_eq]
  constructor
  · rintro ⟨_, ⟨k, ⟨_, moved⟩, _, ⟨_, member⟩, rfl⟩, rfl⟩
    exact ⟨k, member, moved⟩
  · rintro ⟨k, member, moved⟩
    exact ⟨(k, j), ⟨k, ⟨⟨_, entry, member⟩, moved⟩, j, ⟨present, member⟩, rfl⟩,
      rfl⟩

/-- Each row of the subscriber-table machine is the push state of that decision. -/
theorem pushDirty_eq_dirty {ver : Cut steps → K → ℕ} {population : Population K} {j : ℕ}
    (present : j < population.length) (t0 t : Cut steps) :
    pushDirty ver population t0 t j = dirty ver (population.getD j []) t0 t := by
  simp only [pushDirty, dirty, notified_eq present]

/-- For monotone counters, the push machine marks a decision dirty exactly when
its stamp disagrees. -/
theorem pushDirty_eq_not_checkStamp {ver : Cut steps → K → ℕ}
    (mono : ∀ (i : Fin steps) k, ver i.castSucc k ≤ ver i.succ k)
    {population : Population K} {j : ℕ} (present : j < population.length) {t0 t : Cut steps}
    (le : t0 ≤ t) :
    pushDirty ver population t0 t j =
      !checkStamp ver t ((population.getD j []).map fun k => (k, ver t0 k)) := by
  rw [pushDirty_eq_dirty present]
  have same := dirty_iff_not_stampAgrees mono le (population.getD j [])
  rw [← checkStamp_iff] at same
  cases dirtyBit : dirty ver (population.getD j []) t0 t <;>
    cases checked : checkStamp ver t ((population.getD j []).map fun k => (k, ver t0 k)) <;>
    simp_all

end Population

/-! ## Pull and push as probe schedules -/

section Schedules

variable {steps : ℕ} {K : Type w}

/-- **Pull** as a probe schedule: every use compares the whole stamp; a miss costs
nothing more. -/
abbrev pullWork {Moment : Type*} (stampLength : ℕ) (reference : Moment) (uses : List Moment) :
    ℕ :=
  queryWork (fun _ _ => false) .epoch stampLength 0 reference uses

theorem pullWork_eq {Moment : Type*} (stampLength : ℕ) (reference : Moment) (uses : List Moment) :
    pullWork stampLength reference uses = stampLength * uses.length := by
  simp [queryWork]

/-- The counter of `k` moved at the step ending at cut `c`. -/
def movedInto (ver : Cut steps → K → ℕ) (k : K) (c : Cut steps) : Bool :=
  Fin.cases false (fun i => movedAt ver i k) c

/-- Every step of the history, as the cut it ends at. -/
def stepCuts (steps : ℕ) : List (Cut steps) :=
  (List.finRange steps).map Fin.succ

/-- **Push** as a probe schedule for one subscribed class: an event at every step,
paying nothing, and a probe, the notification, exactly when the counter moved. -/
abbrev pushWork (ver : Cut steps → K → ℕ) (k : K) : ℕ :=
  queryWork (fun _ c => movedInto ver k c) .refreshing 0 1 0 (stepCuts steps)

/-- Push for one class counts the moves of its counter. -/
theorem pushWork_eq (ver : Cut steps → K → ℕ) (k : K) :
    pushWork ver k = (List.finRange steps).countP fun i => movedAt ver i k := by
  simp only [queryWork, Nat.zero_mul, Nat.zero_add, Nat.one_mul, gaps_of_event, stepCuts,
    List.countP_map]
  rfl

/-- Summing a constant over the elements satisfying a predicate. -/
theorem sum_map_ite_const {α : Type*} (p : α → Bool) (c : ℕ) (l : List α) :
    (l.map fun a => if p a then c else 0).sum = c * l.countP p := by
  induction l with
  | nil => simp
  | cons a l ih =>
      rw [List.map_cons, List.sum_cons, ih, List.countP_cons, Nat.mul_add]
      split_ifs <;> simp [Nat.add_comm]

theorem sum_map_filter {α : Type*} (p : α → Bool) (f : α → ℕ) (l : List α) :
    ((l.filter p).map f).sum = (l.map fun a => if p a then f a else 0).sum := by
  induction l with
  | nil => rfl
  | cons a l ih =>
      by_cases holds : p a <;> simp [holds, ih]

theorem sum_map_sum_map_comm {α β : Type*} (f : α → β → ℕ) (l : List α) (m : List β) :
    (l.map fun a => (m.map fun b => f a b).sum).sum =
      (m.map fun b => (l.map fun a => f a b).sum).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih, List.sum_map_add]

variable [DecidableEq K]

/-- The operational push cost of a population: the notifications of every step. -/
def pushNotifications (ver : Cut steps → K → ℕ) (population : Population K) : ℕ :=
  ((List.finRange steps).map fun i => (notifications ver population i).length).sum

/-- **The subscriber table is the push schedule of every class, once per
subscriber.** -/
theorem pushNotifications_eq (ver : Cut steps → K → ℕ) (population : Population K) :
    pushNotifications ver population =
      ((subscribedClasses population).map fun k =>
        (subscribers population k).length * pushWork ver k).sum := by
  have perStep : ∀ i : Fin steps, (notifications ver population i).length =
      ((subscribedClasses population).map fun k =>
        if movedAt ver i k then (subscribers population k).length else 0).sum := by
    intro i
    rw [notifications, List.length_flatMap, movedClasses, sum_map_filter]
    simp only [List.length_map]
  unfold pushNotifications
  simp only [perStep]
  rw [sum_map_sum_map_comm]
  congr 1
  apply List.map_congr_left
  intro k _
  rw [pushWork_eq, ← sum_map_ite_const]

end Schedules

/-! ## The hybrid check -/

section Hybrid

variable {steps : ℕ} {K : Type w}

/-- Compare the global counter with its recorded value; compare the stamp only
when the global counter moved. Returns the reuse decision and the number of
comparisons. -/
def hybridCheck (globalVer : Cut steps → Unit → ℕ) (ver : Cut steps → K → ℕ)
    (t : Cut steps)
    (global : ℕ) (stamp : Stamp K) : Bool × ℕ :=
  if globalVer t () = global then (true, 1) else (checkStamp ver t stamp, 1 + stamp.length)

/-- The hybrid over a sequence of uses: the global counter and the class stamp are
recorded at the reference, which moves by the policy. -/
def hybridRun (globalVer : Cut steps → Unit → ℕ) (ver : Cut steps → K → ℕ)
    (subscribed : List K) (policy : Reference) : Cut steps → List (Cut steps) → ℕ
  | _, [] => 0
  | reference, t :: rest =>
      (hybridCheck globalVer ver t (globalVer reference ())
          (subscribed.map fun k => (k, ver reference k))).2 +
        hybridRun globalVer ver subscribed policy (policy.next reference t) rest

/-- **The hybrid is a probe schedule**: read price one, exact price the stamp
length, misses where the global counter moved since the reference. -/
theorem hybridRun_eq_queryWork (globalVer : Cut steps → Unit → ℕ)
    (ver : Cut steps → K → ℕ)
    (subscribed : List K) (policy : Reference) (reference : Cut steps) (uses : List (Cut steps)) :
    hybridRun globalVer ver subscribed policy reference uses =
      queryWork (changed fun t => globalVer t ()) policy 1 subscribed.length reference uses := by
  induction uses generalizing reference with
  | nil => rfl
  | cons t uses ih =>
      rw [hybridRun, ih]
      unfold queryWork
      rw [gaps_cons]
      simp only [hybridCheck, changed, List.length_cons, List.length_map]
      by_cases same : globalVer reference () = globalVer t ()
      · rw [if_pos same.symm]
        simp only [same, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, if_false,
          Nat.mul_add]
        omega
      · rw [if_neg (Ne.symm same)]
        simp only [same, ne_eq, not_false_eq_true, decide_true, if_true, Nat.mul_add]
        omega

variable {Key : Type u} {Value : Type v} {store : History steps Key Value}
variable {globalVer : Cut steps → Unit → ℕ}

/-- The hybrid decides exactly as pull with the class stamp. -/
theorem hybridCheck_exact [DecidableEq K] {cls : Key → K} {ver : Cut steps → K → ℕ}
    (global : IsVersioning store globalClass globalVer) (exact : IsExact store cls ver)
    {t0 t : Cut steps} (le : t0 ≤ t) (reads : Reads Key Value) :
    (hybridCheck globalVer ver t (globalVer t0 ()) (takeStamp cls ver t0 reads)).1 =
      checkStamp ver t (takeStamp cls ver t0 reads) := by
  unfold hybridCheck
  split_ifs with same
  · have globalAgrees : StampAgrees globalVer t (takeStamp globalClass globalVer t0 reads) :=
      stampAgrees_takeStamp_iff.mpr fun _ _ => same
    exact ((checkStamp_iff _ _ _).mpr (stampAgrees_of_refines global exact
      (refines_globalClass cls) le globalAgrees)).symm
  · rfl

/-- **The refreshing hybrid never costs more than the epoch hybrid**, from
`gaps_refreshing_le_epoch`: a monotone global counter is stable on intervals. -/
theorem hybridRun_refreshing_le_epoch (global : IsVersioning store globalClass globalVer)
    (ver : Cut steps → K → ℕ) (subscribed : List K) {t0 : Cut steps} {uses : List (Cut steps)}
    (sorted : List.IsChain (· ≤ ·) (t0 :: uses)) :
    hybridRun globalVer ver subscribed .refreshing t0 uses ≤
      hybridRun globalVer ver subscribed .epoch t0 uses := by
  rw [hybridRun_eq_queryWork, hybridRun_eq_queryWork]
  unfold queryWork
  apply Nat.add_le_add_left
  apply Nat.mul_le_mul_left
  apply gaps_refreshing_le_epoch _ _ sorted
  intro a b c ab bc same
  have lower := global.stamp_mono () ab
  have upper := global.stamp_mono () bc
  simp only at lower upper same ⊢
  omega

/-- **One comparison per use while nothing changed**, under either policy. -/
theorem hybridRun_quiet (exactGlobal : IsExact store globalClass globalVer)
    (ver : Cut steps → K → ℕ) (subscribed : List K) (policy : Reference) {t0 : Cut steps}
    {uses : List (Cut steps)}
    (quiet : ∀ t ∈ uses, t0 ≤ t ∧ ∀ i : Fin steps, t0 ≤ i.castSucc → i.succ ≤ t →
      store i.succ = store i.castSucc) :
    hybridRun globalVer ver subscribed policy t0 uses = uses.length := by
  have stable : ∀ t ∈ t0 :: uses, globalVer t () = globalVer t0 () := by
    intro t member
    rcases List.mem_cons.mp member with rfl | later
    · rfl
    · obtain ⟨le, unchanged⟩ := quiet t later
      exact exactGlobal.version_eq le fun i lo hi changed =>
        classChangedAt_globalClass_iff.mp changed (unchanged i lo hi)
  rw [hybridRun_eq_queryWork]
  unfold queryWork
  rw [gaps_eq_zero fun before beforeMember after afterMember => by
    simp [changed, stable before beforeMember, stable after (List.mem_cons_of_mem _ afterMember)]]
  simp

end Hybrid

/-! ## The validating strategy as a probe schedule -/

section Strategy

variable {steps : ℕ} {Key : Type u} {Value : Type v} {K : Type w} [DecidableEq K]

/-- The counters of the classes of the listed keys, at cut `t`. -/
def classMark (cls : Key → K) (ver : Cut steps → K → ℕ) (keys : List Key) (t : Cut steps) :
    List ℕ :=
  ((keys.map cls).dedup).map fun k => ver t k

/-- A taken stamp agrees exactly when the class mark is unchanged. -/
theorem stampAgrees_iff_classMark {cls : Key → K} {ver : Cut steps → K → ℕ}
    {t0 t : Cut steps} {reads : Reads Key Value} :
    StampAgrees ver t (takeStamp cls ver t0 reads) ↔
      classMark cls ver (reads.map Prod.fst) t = classMark cls ver (reads.map Prod.fst) t0 := by
  unfold takeStamp classMark
  rw [stampAgrees_map_iff, List.map_inj_left, classes_eq_keys]

/-- Refinement gives the covering hypothesis of `global_miss_gap`: an unchanged
coarse mark implies an unchanged refined mark, at any two cuts. -/
theorem classMark_covers {K' : Type*} [DecidableEq K'] {store : History steps Key Value}
    {coarse : Key → K} {fine : Key → K'} {verC : Cut steps → K → ℕ}
    {verF : Cut steps → K' → ℕ}
    (versioning : IsVersioning store coarse verC) (exact : IsExact store fine verF)
    (refines : Refines fine coarse) (keys : List Key) :
    ∀ a b, classMark coarse verC keys a = classMark coarse verC keys b →
      classMark fine verF keys a = classMark fine verF keys b := by
  let reads : Reads Key Value := keys.map fun key => (key, store 0 key)
  have sameKeys : reads.map Prod.fst = keys := by simp [reads, Function.comp_def]
  intro a b same
  rcases le_total a b with ab | ba
  · have agrees : StampAgrees verC b (takeStamp coarse verC a reads) := by
      rw [stampAgrees_iff_classMark, sameKeys]
      exact same.symm
    have refined := stampAgrees_of_refines versioning exact refines ab agrees
    rw [stampAgrees_iff_classMark, sameKeys] at refined
    exact refined.symm
  · have agrees : StampAgrees verC a (takeStamp coarse verC b reads) := by
      rw [stampAgrees_iff_classMark, sameKeys]
      exact same
    have refined := stampAgrees_of_refines versioning exact refines ba agrees
    rw [stampAgrees_iff_classMark, sameKeys] at refined
    exact refined

/-- The uses that did not reuse on the stamp: restamps and recomputations. -/
def alarmCount {Answer : Type*} : List (Observation Key Value Answer × Outcome) → ℕ
  | [] => 0
  | result :: rest => (if result.2 = .reused then 0 else 1) + alarmCount rest

/-- The comparisons of the validating strategy: the stamp at every use, and the
reads at every alarm. -/
def strategyWork {Answer : Type*} (stampLength readLength : ℕ) :
    List (Observation Key Value Answer × Outcome) → ℕ
  | [] => 0
  | result :: rest =>
      stampLength + (if result.2 = .reused then 0 else readLength) +
        strategyWork stampLength readLength rest

theorem strategyWork_eq {Answer : Type*} (stampLength readLength : ℕ)
    (results : List (Observation Key Value Answer × Outcome)) :
    strategyWork stampLength readLength results =
      stampLength * results.length + readLength * alarmCount results := by
  induction results with
  | nil => rfl
  | cons result rest ih =>
      rw [strategyWork, alarmCount, ih, List.length_cons, Nat.mul_add, Nat.mul_add]
      split_ifs <;> omega

variable [DecidableEq Value]

theorem serve_length {Answer : Type*} {store : History steps Key Value} {cls : Key → K}
    {ver : Cut steps → K → ℕ} (program : Program Key Value Answer)
    (decision : Decision K Key Value Answer) (times : List (Cut steps)) :
    (serve cls ver store program decision times).length = times.length := by
  induction times generalizing decision with
  | nil => rfl
  | cons t times ih => simp [serve, ih]

/-- **Alarms are refreshing misses.** For a query whose read keys do not depend on
the store, the strategy fails its stamp check exactly at the uses at which the
class mark moved since the previous use. -/
theorem alarmCount_serve_eq_gaps {Answer : Type*} {store : History steps Key Value}
    {cls : Key → K} {ver : Cut steps → K → ℕ} (versioning : IsVersioning store cls ver)
    (program : Program Key Value Answer) {keys : List Key}
    (fixed : ∀ current : Key → Value, (run current program).reads.map Prod.fst = keys)
    {t0 : Cut steps} {times : List (Cut steps)} (sorted : List.IsChain (· ≤ ·) (t0 :: times)) :
    alarmCount (serve cls ver store program (record cls ver store program t0) times) =
      gaps (changed (classMark cls ver keys)) .refreshing t0 times := by
  induction times generalizing t0 with
  | nil => rfl
  | cons t times ih =>
      obtain ⟨le, rest⟩ := List.isChain_cons_cons.mp sorted
      have reusedIff := use_reused_iff (cls := cls) (ver := ver) (store := store) program t0 t
      rw [stampAgrees_iff_classMark, fixed] at reusedIff
      simp only [serve, alarmCount, use_record versioning program le, ih rest, gaps_cons,
        Reference.next, changed]
      congr 1
      by_cases same : classMark cls ver keys t0 = classMark cls ver keys t
      · rw [if_pos (reusedIff.mpr same.symm)]
        simp [same]
      · rw [if_neg (fun reused => same (reusedIff.mp reused).symm)]
        simp [same]

/-- **The validating strategy is a probe schedule**: read price the stamp length,
exact price the read check, refreshing misses of the class mark. -/
theorem strategyWork_eq_queryWork {Answer : Type*} {store : History steps Key Value}
    {cls : Key → K} {ver : Cut steps → K → ℕ} (versioning : IsVersioning store cls ver)
    (program : Program Key Value Answer) {keys : List Key}
    (fixed : ∀ current : Key → Value, (run current program).reads.map Prod.fst = keys)
    {t0 : Cut steps} {times : List (Cut steps)} (sorted : List.IsChain (· ≤ ·) (t0 :: times)) :
    strategyWork ((keys.map cls).dedup.length) keys.length
        (serve cls ver store program (record cls ver store program t0) times) =
      queryWork (changed (classMark cls ver keys)) .refreshing ((keys.map cls).dedup.length)
        keys.length t0 times := by
  rw [strategyWork_eq, serve_length, alarmCount_serve_eq_gaps versioning program fixed sorted]
  rfl

/-- **Global alarms are class alarms plus unrelated gaps**, from `global_miss_gap`
with the covering hypothesis supplied by refinement. -/
theorem global_alarms_eq {Answer : Type*} {store : History steps Key Value} {cls : Key → K}
    {ver : Cut steps → K → ℕ} {globalVer : Cut steps → Unit → ℕ}
    (global : IsVersioning store globalClass globalVer) (versioning : IsVersioning store cls ver)
    (exact : IsExact store cls ver) (program : Program Key Value Answer) {keys : List Key}
    (fixed : ∀ current : Key → Value, (run current program).reads.map Prod.fst = keys)
    {t0 : Cut steps} {times : List (Cut steps)} (sorted : List.IsChain (· ≤ ·) (t0 :: times)) :
    alarmCount (serve globalClass globalVer store program
        (record globalClass globalVer store program t0) times) =
      alarmCount (serve cls ver store program (record cls ver store program t0) times) +
        gaps (onlyCoarseChanged (classMark globalClass globalVer keys) (classMark cls ver keys))
          .refreshing t0 times := by
  rw [alarmCount_serve_eq_gaps global program fixed sorted,
    alarmCount_serve_eq_gaps versioning program fixed sorted]
  exact global_miss_gap _ _ (classMark_covers global exact (refines_globalClass cls) keys)
    .refreshing t0 times

end Strategy

/-! ## Families: neither push nor pull dominates -/

section Families

/-- Read the listed keys in order and return their values. -/
def readAll {Key : Type u} {Value : Type v} : List Key → Program Key Value (List Value)
  | [] => .pure []
  | key :: keys => .read key fun value => map (value :: ·) (readAll keys)

theorem run_readAll {Key : Type u} {Value : Type v} (store : Key → Value) (keys : List Key) :
    run store (readAll keys) = ⟨keys.map store, keys.map fun key => (key, store key)⟩ := by
  induction keys with
  | nil => rfl
  | cons key keys ih => simp only [readAll, run, run_map, ih, List.map_cons]

/-- Nothing ever changes. -/
def quiet (m : ℕ) : History m ℕ ℕ := fun _ _ => 0

/-- Key 0 changes at every step; no other key changes. -/
def churn (m : ℕ) : History m ℕ ℕ := fun t n => if n = 0 then t else 0

open Classical in
theorem countingVersion_quiet (m : ℕ) (t : Cut m) (k : ℕ) :
    countingVersion (quiet m) perKeyClass t k = 0 := by
  induction t using Fin.induction with
  | zero => exact countingVersion_zero k
  | succ i ih =>
      rw [countingVersion_succ, ih, if_neg]
      rw [classChangedAt_perKeyClass_iff]
      exact fun changed => changed rfl

open Classical in
theorem countingVersion_churn (m : ℕ) (t : Cut m) (k : ℕ) :
    countingVersion (churn m) perKeyClass t k = if k = 0 then (t : ℕ) else 0 := by
  induction t using Fin.induction with
  | zero =>
      rw [countingVersion_zero]
      split_ifs <;> rfl
  | succ i ih =>
      rw [countingVersion_succ, ih]
      by_cases zero : k = 0
      · subst zero
        rw [if_pos (classChangedAt_perKeyClass_iff.mpr (by simp [churn]))]
        simp
      · have quietStep : ¬ ClassChangedAt (churn m) perKeyClass k i := by
          rw [classChangedAt_perKeyClass_iff]
          simp [churn, zero]
        rw [if_neg quietStep]
        simp [zero]

/-- Read-heavy: one decision reads the keys `0, …, m - 1` of the quiet history
and is used at every cut after the first. -/
def readHeavyReads (m : ℕ) : Reads ℕ ℕ :=
  (run (quiet m 0) (readAll (List.range m))).reads

/-- Write-heavy: one decision reads key 0 of the churning history. -/
def writeHeavyReads (m : ℕ) : Reads ℕ ℕ :=
  (run (churn m 0) (readAll [0])).reads

theorem classes_readHeavyReads (m : ℕ) :
    classes perKeyClass (readHeavyReads m) = List.range m := by
  simp only [readHeavyReads, classes, run_readAll, List.map_map]
  exact (List.map_id' _).symm ▸ List.nodup_range.dedup

theorem classes_writeHeavyReads (m : ℕ) : classes perKeyClass (writeHeavyReads m) = [0] := by
  simp [writeHeavyReads, classes, run_readAll, perKeyClass]

open Classical in
theorem readHeavy_costs (m : ℕ) :
    pullWork (classes perKeyClass (readHeavyReads m)).length (0 : Cut m) (stepCuts m) = m * m ∧
      ((classes perKeyClass (readHeavyReads m)).map
        (pushWork (countingVersion (quiet m) perKeyClass))).sum = 0 ∧
      hybridRun (countingVersion (quiet m) globalClass) (countingVersion (quiet m) perKeyClass)
        (classes perKeyClass (readHeavyReads m)) .epoch 0 (stepCuts m) = m := by
  refine ⟨?_, ?_, ?_⟩
  · rw [pullWork_eq, classes_readHeavyReads]
    simp [stepCuts]
  · apply List.sum_eq_zero
    intro cost member
    obtain ⟨k, _, rfl⟩ := List.mem_map.mp member
    rw [pushWork_eq, List.countP_eq_zero]
    intro i _
    simp [movedAt, countingVersion_quiet]
  · rw [hybridRun_quiet countingVersion_isExact]
    · simp [stepCuts]
    · intro t _
      exact ⟨Fin.zero_le _, fun _ _ _ => rfl⟩

open Classical in
theorem writeHeavy_costs (m : ℕ) :
    pullWork (classes perKeyClass (writeHeavyReads m)).length (0 : Cut m) [Fin.last m] = 1 ∧
      ((classes perKeyClass (writeHeavyReads m)).map
        (pushWork (countingVersion (churn m) perKeyClass))).sum = m := by
  rw [classes_writeHeavyReads]
  refine ⟨by simp [pullWork_eq], ?_⟩
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
  rw [pushWork_eq, List.countP_eq_length.mpr]
  · exact List.length_finRange
  · intro i _
    simp [movedAt, countingVersion_churn]

open Classical in
/-- **Neither push nor pull dominates.** No constant factor bounds pull by push,
even with push charged one dirty-bit test per use, and none bounds push by pull. -/
theorem neither_dominates :
    (∀ c : ℕ, ∃ m,
      c * (((classes perKeyClass (readHeavyReads m)).map
          (pushWork (countingVersion (quiet m) perKeyClass))).sum + (stepCuts m).length) <
        pullWork (classes perKeyClass (readHeavyReads m)).length (0 : Cut m) (stepCuts m)) ∧
      (∀ c : ℕ, ∃ m,
        c * pullWork (classes perKeyClass (writeHeavyReads m)).length (0 : Cut m) [Fin.last m] <
          ((classes perKeyClass (writeHeavyReads m)).map
            (pushWork (countingVersion (churn m) perKeyClass))).sum) := by
  refine ⟨fun c => ⟨c + 1, ?_⟩, fun c => ⟨c + 1, ?_⟩⟩
  · obtain ⟨pull, push, _⟩ := readHeavy_costs (c + 1)
    rw [pull, push]
    simp only [stepCuts, List.length_map, List.length_finRange, Nat.zero_add]
    exact Nat.mul_lt_mul_of_pos_right (Nat.lt_succ_self c) (Nat.succ_pos c)
  · obtain ⟨pull, push⟩ := writeHeavy_costs (c + 1)
    rw [pull, push, Nat.mul_one]
    exact Nat.lt_succ_self c

end Families

namespace Controls

/-- `push_eq_pull` and `push_sound` apply with their hypotheses met: across the
unrelated change the per-key decision is clean and its stamp agrees. -/
theorem push_instance :
    dirty (countingVersion unrelatedChange perKeyClass)
        (classes perKeyClass (run (unrelatedChange 0) readFalse).reads) 0 1 = false ∧
      checkStamp (countingVersion unrelatedChange perKeyClass) 1
        (takeStamp perKeyClass (countingVersion unrelatedChange perKeyClass) 0
          (run (unrelatedChange 0) readFalse).reads) = true ∧
      dirty (countingVersion readChange perKeyClass)
        (classes perKeyClass (run (readChange 0) readFalse).reads) 0 1 = true := by
  decide

theorem push_sound_instance :
    run (unrelatedChange 1) readFalse = run (unrelatedChange 0) readFalse :=
  push_reuse_sound (fun i n changed =>
      Nat.ne_of_lt (countingVersion_isVersioning.covering i n changed))
    (Fin.zero_le _) readFalse push_instance.1

/-- The hybrid check applies with its hypotheses met: the unrelated change moves
the global counter, and the hybrid falls back to the per-key stamp, which agrees,
after two comparisons. -/
theorem hybrid_instance :
    hybridCheck (countingVersion unrelatedChange globalClass)
        (countingVersion unrelatedChange perKeyClass) 1
        (countingVersion unrelatedChange globalClass 0 ())
        (takeStamp perKeyClass (countingVersion unrelatedChange perKeyClass) 0
          (run (unrelatedChange 0) readFalse).reads) = (true, 2) ∧
      (hybridCheck (countingVersion unrelatedChange globalClass)
          (countingVersion unrelatedChange perKeyClass) 1
          (countingVersion unrelatedChange globalClass 0 ())
          (takeStamp perKeyClass (countingVersion unrelatedChange perKeyClass) 0
            (run (unrelatedChange 0) readFalse).reads)).1 =
        checkStamp (countingVersion unrelatedChange perKeyClass) 1
          (takeStamp perKeyClass (countingVersion unrelatedChange perKeyClass) 0
            (run (unrelatedChange 0) readFalse).reads) :=
  ⟨by decide, hybridCheck_exact countingVersion_isVersioning countingVersion_isExact
    (Fin.zero_le _) _⟩

/-- Two retained decisions, reading key `false` and key `true`. -/
def twoDecisions : Population Bool := [[false], [true]]

/-- The subscriber-table machine on the unrelated change: one notification, to the
decision subscribed to `true`, which alone becomes dirty. -/
theorem population_instance :
    notifications (countingVersion unrelatedChange perKeyClass) twoDecisions 0 = [(true, 1)] ∧
      pushDirty (countingVersion unrelatedChange perKeyClass) twoDecisions 0 1 0 = false ∧
      pushDirty (countingVersion unrelatedChange perKeyClass) twoDecisions 0 1 1 = true ∧
      pushNotifications (countingVersion unrelatedChange perKeyClass) twoDecisions = 1 ∧
      pushNotifications (countingVersion unrelatedChange perKeyClass) twoDecisions =
        ((subscribedClasses twoDecisions).map fun k =>
          (subscribers twoDecisions k).length *
            pushWork (countingVersion unrelatedChange perKeyClass) k).sum ∧
      pushDirty (countingVersion unrelatedChange perKeyClass) twoDecisions 0 1 1 =
        !checkStamp (countingVersion unrelatedChange perKeyClass) 1
          ((twoDecisions.getD 1 []).map fun k =>
            (k, countingVersion unrelatedChange perKeyClass 0 k)) :=
  ⟨by decide, by decide, by decide, by decide, pushNotifications_eq _ _,
    pushDirty_eq_not_checkStamp countingVersion_isVersioning.advance (by decide)
      (Fin.zero_le _)⟩

/-- `alarmCount_serve_eq_gaps` and `global_alarms_eq` apply with their hypotheses
met on the mixed history: two global alarms, one class alarm, one unrelated gap. -/
theorem mixed_alarms :
    alarmCount (serve globalClass (countingVersion mixed globalClass) mixed readFalse
        (record globalClass (countingVersion mixed globalClass) mixed readFalse 0)
        [1, 2, 3]) = 2 ∧
      alarmCount (serve perKeyClass (countingVersion mixed perKeyClass) mixed readFalse
        (record perKeyClass (countingVersion mixed perKeyClass) mixed readFalse 0)
        [1, 2, 3]) = 1 ∧
      gaps (onlyCoarseChanged (classMark globalClass (countingVersion mixed globalClass) [false])
        (classMark perKeyClass (countingVersion mixed perKeyClass) [false])) .refreshing 0
        [1, 2, 3] = 1 ∧
      alarmCount (serve globalClass (countingVersion mixed globalClass) mixed readFalse
          (record globalClass (countingVersion mixed globalClass) mixed readFalse 0) [1, 2, 3]) =
        alarmCount (serve perKeyClass (countingVersion mixed perKeyClass) mixed readFalse
          (record perKeyClass (countingVersion mixed perKeyClass) mixed readFalse 0) [1, 2, 3]) +
        gaps (onlyCoarseChanged (classMark globalClass (countingVersion mixed globalClass) [false])
          (classMark perKeyClass (countingVersion mixed perKeyClass) [false])) .refreshing 0
          [1, 2, 3] :=
  ⟨by decide, by decide, by decide,
    global_alarms_eq countingVersion_isVersioning countingVersion_isVersioning
      countingVersion_isExact readFalse (fun _ => rfl) (by decide)⟩

/-- After one early unrelated change, the epoch hybrid pays the fallback at every
use and the refreshing hybrid once. -/
theorem epoch_hybrid_exceeds_refreshed :
    hybridRun (countingVersion unrelatedChange globalClass)
        (countingVersion unrelatedChange perKeyClass) [false] .epoch 0 [1, 2, 3] = 6 ∧
      hybridRun (countingVersion unrelatedChange globalClass)
        (countingVersion unrelatedChange perKeyClass) [false] .refreshing 0 [1, 2, 3] = 4 := by
  decide

/-- Key `true` changes at every step; key `false` never changes. -/
def everyStep : History 8 Bool ℕ := fun t n => if n = true then t else 0

/-- Eight moves of the global counter between uses at 0, 3, 3 and 8 cost a
refreshing probe two misses and push eight notifications; the class of the read
key never moves, so both misses are unrelated gaps. -/
theorem gaps_not_moves :
    gaps (changed fun t => countingVersion everyStep globalClass t ()) .refreshing 0
        [0, 3, 3, 8] = 2 ∧
      pushWork (countingVersion everyStep globalClass) () = 8 ∧
      gaps (changed (classMark perKeyClass (countingVersion everyStep perKeyClass) [false]))
        .refreshing 0 [0, 3, 3, 8] = 0 ∧
      gaps (onlyCoarseChanged
          (classMark globalClass (countingVersion everyStep globalClass) [false])
        (classMark perKeyClass (countingVersion everyStep perKeyClass) [false])) .refreshing 0
        [0, 3, 3, 8] = 2 := by
  decide

/-- A value that changes at every step. -/
def ticking : History 2 Unit ℕ := fun t _ => t

/-- A one-bit counter: it changes at every step and wraps around. -/
def oneBit : Cut 2 → Unit → ℕ := fun t _ => (t : ℕ) % 2

def readUnit : Program Unit ℕ ℕ := .read () fun value => .pure value

/-- A wrapping counter signals every change, so push marks the decision dirty;
pull sees the counter back at its recorded value and accepts stale reads. The
counter is not a versioning. -/
theorem wrapping_counter_breaks_pull :
    (∀ (i : Fin 2) n, ticking i.succ n ≠ ticking i.castSucc n →
        oneBit i.castSucc (perKeyClass n) ≠ oneBit i.succ (perKeyClass n)) ∧
      dirty oneBit (classes perKeyClass (run (ticking 0) readUnit).reads) 0 2 = true ∧
      StampAgrees oneBit 2 (takeStamp perKeyClass oneBit 0 (run (ticking 0) readUnit).reads) ∧
      checkReads (ticking 2) (run (ticking 0) readUnit).reads = false ∧
      ¬ IsVersioning ticking perKeyClass oneBit := by
  refine ⟨fun i _ _ => ?_, by decide, by decide, by decide, fun versioning => ?_⟩
  · simp only [oneBit, Fin.val_castSucc, Fin.val_succ]
    omega
  · have bumped := versioning.covering 1 () (by decide)
    revert bumped
    decide

end Controls

end Mettapedia.Machines.VersionedValidation
