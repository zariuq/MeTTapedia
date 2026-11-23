import Mettapedia.Machines.VersionedValidation.Versions

/-!
# Granularity of version classes

A class map `fine` refines `coarse` when the coarse class of every key is a
function of its fine class. The constant class map (one global counter) is the
coarsest; the identity (a counter per key) is the finest.

Refining never adds an alarm (`stampAgrees_of_refines`): if a stamp under any
versioning of the coarse map agrees, the stamp under an exact versioning of the
fine map agrees as well. In particular a global counter checked first, in front
of class counters, never changes the outcome of the class check
(`fastPath_exact`). The canonical counting versioning is exact, and it is the
least alarming versioning of its own class map (`countingVersion_least_alarming`).
Exactness is needed: a counter that moves at every step is a versioning of every
history, and it alarms on every use (`Controls.clock_versioning_alarms`).

Even a counter per key raises false alarms. A key that changes and changes back
restores the value read, but its counter has moved (`Controls.change_back_alarms`).

## Partial class maps

The class map must be total. A design that versions only the names installed
when the stamp is taken gives an absent name no class, so a read of that name
leaves no entry in the stamp. Installing the name later does not touch the stamp,
and reuse returns a stale answer (`Controls.installed_heads_only_is_stale`),
although the counters themselves form a valid versioning.
A footprint of several regions generalizes the class of a key
(`Controls.two_region_footprint`). Partial stamps are sound
exactly as long as every read key has a class (`partial_reuse_sound`). A total
class map into a fixed number of shards, applied to every name, keeps soundness
(`Controls.shards_alarm_on_install`). Counting only changes of installed names is
another form of the same defect: it breaks the covering law at the install
(`Controls.installed_only_counter_not_versioning`).
-/

set_option autoImplicit false

namespace Mettapedia.Machines.VersionedValidation

open ReadOnlyQuery
open Mettapedia.GSLT.Contracts.ReadWindowCuts (Cut Discipline)

universe u v w x

section Refinement

variable {Key : Type u} {Value : Type v} {K : Type w} {K' : Type x}

/-- `fine` refines `coarse` when the coarse class of a key is a function of its
fine class. -/
def Refines (fine : Key → K') (coarse : Key → K) : Prop :=
  ∃ f : K' → K, coarse = f ∘ fine

theorem Refines.refl (cls : Key → K) : Refines cls cls :=
  ⟨id, rfl⟩

theorem Refines.trans {K'' : Type*} {finest : Key → K''} {fine : Key → K'} {coarse : Key → K}
    (first : Refines finest fine) (second : Refines fine coarse) : Refines finest coarse := by
  obtain ⟨f, rfl⟩ := first
  obtain ⟨g, rfl⟩ := second
  exact ⟨g ∘ f, rfl⟩

/-- The coarsest class map: every key shares one global counter. -/
def globalClass : Key → Unit := fun _ => ()

/-- The finest class map: a counter per key. -/
def perKeyClass : Key → Key := id

theorem refines_globalClass (cls : Key → K) : Refines cls (globalClass : Key → Unit) :=
  ⟨fun _ => (), rfl⟩

theorem perKeyClass_refines (cls : Key → K) : Refines (perKeyClass : Key → Key) cls :=
  ⟨cls, rfl⟩

variable [DecidableEq K] [DecidableEq K'] {steps : ℕ}
variable {store : History steps Key Value} {coarse : Key → K} {fine : Key → K'}
variable {verC : Cut steps → K → ℕ} {verF : Cut steps → K' → ℕ}

/-- **Refining never adds an alarm.** If the stamp under a versioning of `coarse`
agrees, the stamp under an exact versioning of a refinement agrees. -/
theorem stampAgrees_of_refines (versioning : IsVersioning store coarse verC)
    (exact : IsExact store fine verF) (refines : Refines fine coarse) {t0 t : Cut steps}
    (le : t0 ≤ t) {reads : Reads Key Value}
    (agrees : StampAgrees verC t (takeStamp coarse verC t0 reads)) :
    StampAgrees verF t (takeStamp fine verF t0 reads) := by
  obtain ⟨f, rfl⟩ := refines
  rw [stampAgrees_takeStamp_iff] at agrees ⊢
  intro read member
  have same := (agrees read member).symm
  apply exact.version_eq le
  rintro i lo hi ⟨n, sameClass, changed⟩
  apply versioning.not_classChangedAt same lo hi
  exact ⟨n, by simp only [Function.comp_apply, sameClass], changed⟩

/-- The counting form: with counting versionings on both sides, a refined stamp
agrees whenever the coarse stamp does. -/
theorem refines_never_adds_alarms
    [∀ k, DecidablePred (ClassChangedAt store coarse k)]
    [∀ k, DecidablePred (ClassChangedAt store fine k)]
    (refines : Refines fine coarse) {t0 t : Cut steps} (le : t0 ≤ t) {reads : Reads Key Value}
    (agrees : StampAgrees (countingVersion store coarse) t
      (takeStamp coarse (countingVersion store coarse) t0 reads)) :
    StampAgrees (countingVersion store fine) t
      (takeStamp fine (countingVersion store fine) t0 reads) :=
  stampAgrees_of_refines countingVersion_isVersioning countingVersion_isExact refines le agrees

/-- Every false alarm of the refined stamp is a false alarm of the coarse stamp. -/
theorem falseAlarm_of_refines (versioning : IsVersioning store coarse verC)
    (exact : IsExact store fine verF) (refines : Refines fine coarse) {t0 t : Cut steps}
    (le : t0 ≤ t) {reads : Reads Key Value}
    (alarm : FalseAlarm store verF t (takeStamp fine verF t0 reads) reads) :
    FalseAlarm store verC t (takeStamp coarse verC t0 reads) reads :=
  ⟨fun agrees => alarm.1 (stampAgrees_of_refines versioning exact refines le agrees), alarm.2⟩

/-- **The fast path is exact.** Checking a coarse stamp first and falling back
to the refined stamp decides exactly what the refined stamp decides. -/
theorem fastPath_exact (versioning : IsVersioning store coarse verC)
    (exact : IsExact store fine verF) (refines : Refines fine coarse) {t0 t : Cut steps}
    (le : t0 ≤ t) (reads : Reads Key Value) :
    (checkStamp verC t (takeStamp coarse verC t0 reads) ||
        checkStamp verF t (takeStamp fine verF t0 reads)) =
      checkStamp verF t (takeStamp fine verF t0 reads) := by
  cases coarseOk : checkStamp verC t (takeStamp coarse verC t0 reads)
  · rfl
  · exact ((checkStamp_iff _ _ _).mpr (stampAgrees_of_refines versioning exact refines le
      ((checkStamp_iff _ _ _).mp coarseOk))).symm

end Refinement

section Counting

variable {Key : Type u} {Value : Type v} {K : Type w} [DecidableEq K] {steps : ℕ}
variable {store : History steps Key Value} {cls : Key → K}
variable [∀ k, DecidablePred (ClassChangedAt store cls k)]

/-- The counting versioning is the least alarming versioning of its class map:
its stamp agrees whenever the stamp of any other versioning agrees. -/
theorem countingVersion_least_alarming {ver : Cut steps → K → ℕ}
    (versioning : IsVersioning store cls ver) {t0 t : Cut steps} (le : t0 ≤ t)
    {reads : Reads Key Value} (agrees : StampAgrees ver t (takeStamp cls ver t0 reads)) :
    StampAgrees (countingVersion store cls) t
      (takeStamp cls (countingVersion store cls) t0 reads) :=
  stampAgrees_of_refines versioning countingVersion_isExact (Refines.refl cls) le agrees

end Counting

section Extremes

variable {Key : Type u} {Value : Type v} {steps : ℕ} {store : History steps Key Value}

theorem classChangedAt_perKeyClass_iff {k : Key} {i : Fin steps} :
    ClassChangedAt store perKeyClass k i ↔ store i.succ k ≠ store i.castSucc k :=
  ⟨fun ⟨_, same, changed⟩ => same ▸ changed, fun changed => ⟨k, rfl, changed⟩⟩

theorem classChangedAt_globalClass_iff {i : Fin steps} :
    ClassChangedAt store globalClass () i ↔ store i.succ ≠ store i.castSucc := by
  constructor
  · rintro ⟨n, _, changed⟩ same
    exact changed (congrFun same n)
  · intro changed
    by_contra quiet
    apply changed
    funext n
    by_contra different
    exact quiet ⟨n, rfl, different⟩

/-- A nonempty global counting stamp agrees exactly when no key at all changed
at any step since the stamp. -/
theorem global_stampAgrees_iff [∀ k, DecidablePred (ClassChangedAt store globalClass k)]
    {t0 t : Cut steps} (le : t0 ≤ t) {reads : Reads Key Value} (nonempty : reads ≠ []) :
    StampAgrees (countingVersion store globalClass) t
        (takeStamp globalClass (countingVersion store globalClass) t0 reads) ↔
      ∀ i : Fin steps, t0 ≤ i.castSucc → i.succ ≤ t →
        store i.succ = store i.castSucc := by
  rw [stampAgrees_takeStamp_iff]
  obtain ⟨read, member⟩ := List.exists_mem_of_ne_nil reads nonempty
  constructor
  · intro agrees
    have quiet := (countingVersion_eq_iff le).mp (agrees read member).symm
    intro i lo hi
    by_contra changed
    exact quiet i lo hi (classChangedAt_globalClass_iff.mpr changed)
  · intro quiet other _
    apply ((countingVersion_eq_iff le).mpr _).symm
    intro i lo hi changed
    exact classChangedAt_globalClass_iff.mp changed (quiet i lo hi)

variable [DecidableEq Key]

/-- A per-key counting stamp agrees exactly when no read key changed at any
step since the stamp. -/
theorem perKey_stampAgrees_iff [∀ k, DecidablePred (ClassChangedAt store perKeyClass k)]
    {t0 t : Cut steps} (le : t0 ≤ t) {reads : Reads Key Value} :
    StampAgrees (countingVersion store perKeyClass) t
        (takeStamp perKeyClass (countingVersion store perKeyClass) t0 reads) ↔
      ∀ read ∈ reads, ∀ i : Fin steps, t0 ≤ i.castSucc → i.succ ≤ t →
        store i.succ read.1 = store i.castSucc read.1 := by
  rw [stampAgrees_takeStamp_iff]
  apply forall₂_congr
  intro read _
  rw [eq_comm, countingVersion_eq_iff le]
  apply forall_congr'
  intro i
  simp only [classChangedAt_perKeyClass_iff, not_not]
  exact Iff.rfl

end Extremes

/-! ## Partial class maps -/

section PartialClassMaps

variable {Key : Type u} {Value : Type v} {K : Type w} [DecidableEq K] {steps : ℕ}

/-- A stamp under a partial class map: a read of a key without a class leaves no
entry. -/
def takePartialStamp (partialClass : Key → Option K) (ver : Cut steps → K → ℕ)
    (t0 : Cut steps)
    (reads : Reads Key Value) : Stamp K :=
  (reads.filterMap fun read => partialClass read.1).dedup.map fun k => (k, ver t0 k)

theorem takePartialStamp_eq_takeStamp {partialClass : Key → Option K} {cls : Key → K}
    {ver : Cut steps → K → ℕ} {t0 : Cut steps} {reads : Reads Key Value}
    (defined : ∀ read ∈ reads, partialClass read.1 = some (cls read.1)) :
    takePartialStamp partialClass ver t0 reads = takeStamp cls ver t0 reads := by
  have same : (reads.filterMap fun read => partialClass read.1) =
      reads.map fun read => cls read.1 := by
    induction reads with
    | nil => rfl
    | cons read rest ih =>
        simp only [List.filterMap_cons, defined read List.mem_cons_self, List.map_cons,
          ih fun other member => defined other (List.mem_cons_of_mem read member)]
  simp only [takePartialStamp, takeStamp, classes, same]

/-- A partial stamp is sound when every read key of the run has its class. -/
theorem partial_reuse_sound {Answer : Type x} {store : History steps Key Value}
    {partialClass : Key → Option K} {cls : Key → K} {ver : Cut steps → K → ℕ}
    (versioning : IsVersioning store cls ver) {t0 t : Cut steps} (le : t0 ≤ t)
    (program : Program Key Value Answer)
    (defined : ∀ read ∈ (run (store t0) program).reads,
      partialClass read.1 = some (cls read.1))
    (agrees : StampAgrees ver t
      (takePartialStamp partialClass ver t0 (run (store t0) program).reads)) :
    run (store t) program = run (store t0) program := by
  rw [takePartialStamp_eq_takeStamp defined] at agrees
  exact reuse_sound versioning le program agrees

/-- The class map of the names installed in a store, one class per installed
name. An absent name has no class. -/
def installedHeads {Payload : Type v} (current : Key → Option Payload) : Key → Option Key :=
  fun n => if (current n).isSome then some n else none

end PartialClassMaps

/-! ## Controls -/

namespace Controls

/-- Read key `false` and return its value. -/
def readFalse : Program Bool ℕ ℕ :=
  .read false fun value => .pure value

/-- Key `true`, never read, changes at step 0. -/
def unrelatedChange : History 3 Bool ℕ :=
  fun t n => if n = true ∧ 1 ≤ (t : ℕ) then 1 else 0

/-- The read key `false` changes at step 0. -/
def readChange : History 3 Bool ℕ :=
  fun t n => if n = false ∧ 1 ≤ (t : ℕ) then 1 else 0

/-- The read key changes at step 0 and changes back at step 1. -/
def changeBack : History 3 Bool ℕ :=
  fun t n => if n = false ∧ (t : ℕ) = 1 then 1 else 0

/-- Key `true` changes at step 0, the read key at step 2. -/
def mixed : History 3 Bool ℕ :=
  fun t n =>
    if n = true then (if 1 ≤ (t : ℕ) then 1 else 0) else (if 3 ≤ (t : ℕ) then 1 else 0)

/-- An unrelated change alarms the global stamp, falsely, and leaves the per-key
stamp quiet. The strategy restamps under the global counter and reuses under
per-key counters. -/
theorem unrelated_change_alarms_global_only :
    unrelatedChange 1 true ≠ unrelatedChange 0 true ∧
      FalseAlarm unrelatedChange (countingVersion unrelatedChange globalClass) 1
        (takeStamp globalClass (countingVersion unrelatedChange globalClass) 0
          (run (unrelatedChange 0) readFalse).reads)
        (run (unrelatedChange 0) readFalse).reads ∧
      StampAgrees (countingVersion unrelatedChange perKeyClass) 1
        (takeStamp perKeyClass (countingVersion unrelatedChange perKeyClass) 0
          (run (unrelatedChange 0) readFalse).reads) ∧
      (use globalClass (countingVersion unrelatedChange globalClass) unrelatedChange readFalse 1
        (record globalClass (countingVersion unrelatedChange globalClass) unrelatedChange
          readFalse 0)).2 = .restamped ∧
      (use perKeyClass (countingVersion unrelatedChange perKeyClass) unrelatedChange readFalse 1
        (record perKeyClass (countingVersion unrelatedChange perKeyClass) unrelatedChange
          readFalse 0)).2 = .reused :=
  ⟨by decide, ⟨by decide, (checkReads_iff _ _).mp (by decide)⟩, by decide, by decide,
    by decide⟩

/-- `reuse_sound` applies with its hypotheses met although the store changed:
the per-key stamp agrees across the unrelated change. -/
theorem reuse_sound_instance :
    run (unrelatedChange 1) readFalse = run (unrelatedChange 0) readFalse :=
  reuse_sound countingVersion_isVersioning (Fin.zero_le _) readFalse
    unrelated_change_alarms_global_only.2.2.1

/-- A change of the read key alarms both stamps, and both strategies recompute
the new answer. -/
theorem read_change_alarms_both :
    ¬ StampAgrees (countingVersion readChange globalClass) 1
        (takeStamp globalClass (countingVersion readChange globalClass) 0
          (run (readChange 0) readFalse).reads) ∧
      ¬ StampAgrees (countingVersion readChange perKeyClass) 1
        (takeStamp perKeyClass (countingVersion readChange perKeyClass) 0
          (run (readChange 0) readFalse).reads) ∧
      checkReads (readChange 1) (run (readChange 0) readFalse).reads = false ∧
      (use globalClass (countingVersion readChange globalClass) readChange readFalse 1
        (record globalClass (countingVersion readChange globalClass) readChange
          readFalse 0)).2 = .recomputed ∧
      (use perKeyClass (countingVersion readChange perKeyClass) readChange readFalse 1
        (record perKeyClass (countingVersion readChange perKeyClass) readChange
          readFalse 0)).2 = .recomputed ∧
      (run (readChange 0) readFalse).answer = 0 ∧ (run (readChange 1) readFalse).answer = 1 := by
  decide

/-- A change and a change back restore the value read, yet both stamps alarm,
because counters never decrease. The per-key alarm is false: no granularity is
free of false alarms. -/
theorem change_back_alarms :
    changeBack 1 false ≠ changeBack 0 false ∧
      checkReads (changeBack 2) (run (changeBack 0) readFalse).reads = true ∧
      ¬ StampAgrees (countingVersion changeBack globalClass) 2
        (takeStamp globalClass (countingVersion changeBack globalClass) 0
          (run (changeBack 0) readFalse).reads) ∧
      FalseAlarm changeBack (countingVersion changeBack perKeyClass) 2
        (takeStamp perKeyClass (countingVersion changeBack perKeyClass) 0
          (run (changeBack 0) readFalse).reads)
        (run (changeBack 0) readFalse).reads ∧
      (use perKeyClass (countingVersion changeBack perKeyClass) changeBack readFalse 2
        (record perKeyClass (countingVersion changeBack perKeyClass) changeBack
          readFalse 0)).2 = .restamped :=
  ⟨by decide, by decide, by decide, ⟨by decide, (checkReads_iff _ _).mp (by decide)⟩,
    by decide⟩

/-- `stampAgrees_of_refines` applies with its hypotheses met: after the change,
the global stamp taken at time 1 agrees at time 2, and so does the per-key one. -/
theorem refinement_instance :
    StampAgrees (countingVersion unrelatedChange globalClass) 2
        (takeStamp globalClass (countingVersion unrelatedChange globalClass) 1
          (run (unrelatedChange 1) readFalse).reads) ∧
      StampAgrees (countingVersion unrelatedChange perKeyClass) 2
        (takeStamp perKeyClass (countingVersion unrelatedChange perKeyClass) 1
          (run (unrelatedChange 1) readFalse).reads) :=
  ⟨by decide, refines_never_adds_alarms (perKeyClass_refines globalClass) (by decide)
    (by decide)⟩

/-- Serving uses at times 1, 2 and 3 of the mixed history. The global counter
restamps once on the unrelated change, per-key counters never check a read, and
both recompute exactly at time 3 and return the same answers. -/
theorem mixed_serve :
    (serve globalClass (countingVersion mixed globalClass) mixed readFalse
        (record globalClass (countingVersion mixed globalClass) mixed readFalse 0)
        [1, 2, 3]).map Prod.snd = [.restamped, .reused, .recomputed] ∧
      (serve perKeyClass (countingVersion mixed perKeyClass) mixed readFalse
        (record perKeyClass (countingVersion mixed perKeyClass) mixed readFalse 0)
        [1, 2, 3]).map Prod.snd = [.reused, .reused, .recomputed] ∧
      (serve globalClass (countingVersion mixed globalClass) mixed readFalse
        (record globalClass (countingVersion mixed globalClass) mixed readFalse 0)
        [1, 2, 3]).map (fun result => result.1.answer) = [0, 0, 1] ∧
      (serve perKeyClass (countingVersion mixed perKeyClass) mixed readFalse
        (record perKeyClass (countingVersion mixed perKeyClass) mixed readFalse 0)
        [1, 2, 3]).map (fun result => result.1.answer) = [0, 0, 1] ∧
      recomputations mixed readFalse 0 [1, 2, 3] = [false, false, true] := by
  decide

/-- `serve_record` applies with its hypotheses met on the mixed history. -/
theorem serve_record_instance :
    (serve perKeyClass (countingVersion mixed perKeyClass) mixed readFalse
        (record perKeyClass (countingVersion mixed perKeyClass) mixed readFalse 0)
        [1, 2, 3]).map Prod.fst = [1, 2, 3].map fun t => run (mixed t) readFalse :=
  (serve_record countingVersion_isVersioning readFalse (by decide)).1

/-- `falseAlarm_of_refines` applies with its hypotheses met: the per-key false
alarm after a change and a change back is a false alarm of the global stamp. -/
theorem change_back_global_false_alarm :
    FalseAlarm changeBack (countingVersion changeBack globalClass) 2
      (takeStamp globalClass (countingVersion changeBack globalClass) 0
        (run (changeBack 0) readFalse).reads)
      (run (changeBack 0) readFalse).reads :=
  falseAlarm_of_refines countingVersion_isVersioning countingVersion_isExact
    (perKeyClass_refines globalClass) (Fin.zero_le _) change_back_alarms.2.2.2.1

/-- The bridge locality lemma applies with its hypotheses met: the unrelated
change moves only the counter of key `true`, outside the class support. -/
theorem bump_outside_instance :
    true ∉ classSupport perKeyClass (run (unrelatedChange 0) readFalse).reads ∧
      (StampAgrees (countingVersion unrelatedChange perKeyClass) 1
          (takeStamp perKeyClass (countingVersion unrelatedChange perKeyClass) 0
            (run (unrelatedChange 0) readFalse).reads) ↔
        StampAgrees (countingVersion unrelatedChange perKeyClass) 0
          (takeStamp perKeyClass (countingVersion unrelatedChange perKeyClass) 0
            (run (unrelatedChange 0) readFalse).reads)) := by
  have step : countingVersion unrelatedChange perKeyClass (0 : Fin 3).succ =
      Function.update (countingVersion unrelatedChange perKeyClass (0 : Fin 3).castSucc)
        true 1 := by
    funext k
    cases k <;> decide
  exact ⟨by decide, stampAgrees_bump_outside_iff step (by decide)⟩

/-- The bridge invalidation lemma applies with its hypotheses met: changing the
read key moves its counter, inside the class support. -/
theorem bump_inside_instance :
    ¬ StampAgrees (countingVersion readChange perKeyClass) 1
      (takeStamp perKeyClass (countingVersion readChange perKeyClass) 0
        (run (readChange 0) readFalse).reads) := by
  have step : countingVersion readChange perKeyClass (0 : Fin 3).succ =
      Function.update (countingVersion readChange perKeyClass (0 : Fin 3).castSucc) false
        (countingVersion readChange perKeyClass (0 : Fin 3).castSucc false + 1) := by
    funext k
    cases k <;> decide
  exact not_stampAgrees_versioning_bump countingVersion_isVersioning le_rfl step (by decide)

/-- A counter that moves at every step is a versioning of every history. -/
def clock : Cut 3 → Bool → ℕ := fun t _ => t

theorem clock_isVersioning : IsVersioning unrelatedChange perKeyClass clock :=
  IsVersioning.of_laws (fun i _ => by simp [clock]) (fun i _ _ => by simp [clock])

/-- Exactness cannot be dropped from `stampAgrees_of_refines`: the clock is a
valid per-key versioning, yet it alarms where the global counting stamp agrees,
and it is not exact. -/
theorem clock_versioning_alarms :
    StampAgrees (countingVersion unrelatedChange globalClass) 2
        (takeStamp globalClass (countingVersion unrelatedChange globalClass) 1
          (run (unrelatedChange 1) readFalse).reads) ∧
      ¬ StampAgrees clock 2 (takeStamp perKeyClass clock 1
        (run (unrelatedChange 1) readFalse).reads) ∧
      ¬ IsExact unrelatedChange perKeyClass clock := by
  refine ⟨by decide, by decide, fun exact => ?_⟩
  have changed := exact 1 false (by decide)
  revert changed
  decide

/-! ### Footprints of several regions

A class map is the single-region footprint. A key may instead be guarded by a
set of regions, and change while only one of them moves. -/

/-- A key covered by two regions: the first step moves only region `false`, the
second only region `true`. With the footprint of both regions this is a
discipline; with either region alone it is not. -/
def twoRegionView : Cut 2 → Unit → ℕ := fun cut _ => cut

def twoRegionStamp : Cut 2 → Bool → ℕ := fun cut region =>
  if region then (if 2 ≤ (cut : ℕ) then 1 else 0) else (if 1 ≤ (cut : ℕ) then 1 else 0)

theorem two_region_footprint :
    Discipline twoRegionView (fun _ => (Set.univ : Set Bool)) twoRegionStamp ∧
      ¬ Discipline twoRegionView (fun _ => ({false} : Set Bool)) twoRegionStamp ∧
      ¬ Discipline twoRegionView (fun _ => ({true} : Set Bool)) twoRegionStamp := by
  refine ⟨⟨fun i region => ?_, fun i _ same => ?_⟩, fun discipline => ?_,
    fun discipline => ?_⟩
  · fin_cases i <;> cases region <;> decide
  · fin_cases i
    · have moved := same (Set.mem_univ false)
      exact absurd moved (by decide)
    · have moved := same (Set.mem_univ true)
      exact absurd moved (by decide)
  · have frame := discipline.frame 1 () (by
      intro region member
      rw [Set.mem_singleton_iff] at member
      subst member
      decide)
    exact absurd frame (by decide)
  · have frame := discipline.frame 0 () (by
      intro region member
      rw [Set.mem_singleton_iff] at member
      subst member
      decide)
    exact absurd frame (by decide)

/-! ### Installed heads only -/

/-- Key 1 is installed throughout; key 2 is absent at time 0 and installed from
time 1. -/
def installs : History 1 (Fin 4) (Option ℕ) :=
  fun t n => if n = 1 then some 1 else if n = 2 ∧ 1 ≤ (t : ℕ) then some 7 else none

/-- Read key 1, then the absent key 2. -/
def lookupPair : Program (Fin 4) (Option ℕ) (Option ℕ × Option ℕ) :=
  .read 1 fun first => .read 2 fun second => .pure (first, second)

/-- With classes only for the names installed at the stamp, the absent read leaves
no entry. After the install the partial stamp still agrees, under the valid
per-key counting versioning, and reuse returns the stale answer. The total
per-key stamp alarms. -/
theorem installed_heads_only_is_stale :
    (run (installs 0) lookupPair).reads = [(1, some 1), (2, none)] ∧
      takePartialStamp (installedHeads (installs 0)) (countingVersion installs perKeyClass) 0
        (run (installs 0) lookupPair).reads = [(1, 0)] ∧
      StampAgrees (countingVersion installs perKeyClass) 1
        (takePartialStamp (installedHeads (installs 0)) (countingVersion installs perKeyClass) 0
          (run (installs 0) lookupPair).reads) ∧
      (run (installs 0) lookupPair).answer = (some 1, none) ∧
      (run (installs 1) lookupPair).answer = (some 1, some 7) ∧
      ¬ StampAgrees (countingVersion installs perKeyClass) 1
        (takeStamp perKeyClass (countingVersion installs perKeyClass) 0
          (run (installs 0) lookupPair).reads) := by
  decide

/-- `partial_reuse_sound` applies with its hypotheses met: for a run that reads
only installed names the installed-heads stamp is the per-key stamp. -/
theorem installed_heads_sound_instance :
    run (installs 1) (.read 1 fun value => .pure value : Program (Fin 4) (Option ℕ) _) =
      run (installs 0) (.read 1 fun value => .pure value) :=
  partial_reuse_sound (partialClass := installedHeads (installs 0)) (cls := perKeyClass)
    countingVersion_isVersioning (Fin.zero_le _) _
    (by decide) (by decide)

/-- Every name hashed into one of two shards. -/
def shard : Fin 4 → Fin 2 := fun n => ⟨n.val % 2, Nat.mod_lt _ (by decide)⟩

/-- A total class map into a fixed number of shards stamps the absent read, and
the install alarms the stamp. -/
theorem shards_alarm_on_install :
    takeStamp shard (countingVersion installs shard) 0 (run (installs 0) lookupPair).reads =
        [(1, 0), (0, 0)] ∧
      ¬ StampAgrees (countingVersion installs shard) 1
        (takeStamp shard (countingVersion installs shard) 0
          (run (installs 0) lookupPair).reads) := by
  decide

/-- A per-key counter of changes to names that were installed before the change. -/
def installedOnlyVersion (t : Cut 1) (n : Fin 4) : ℕ :=
  Nat.count (fun s => ∃ h : s < 1, (installs (Fin.castSucc ⟨s, h⟩) n).isSome = true ∧
    installs (Fin.succ ⟨s, h⟩) n ≠ installs (Fin.castSucc ⟨s, h⟩) n) t

/-- Counting only changes of installed names breaks the covering law at the
install, and its total per-key stamp then accepts the stale answer. -/
theorem installed_only_counter_not_versioning :
    ¬ IsVersioning installs perKeyClass installedOnlyVersion ∧
      StampAgrees installedOnlyVersion 1
        (takeStamp perKeyClass installedOnlyVersion 0 (run (installs 0) lookupPair).reads) ∧
      (run (installs 1) lookupPair).answer ≠ (run (installs 0) lookupPair).answer := by
  refine ⟨fun versioning => ?_, by decide, by decide⟩
  have bumped := versioning.covering 0 2 (by decide)
  revert bumped
  decide

end Controls

end Mettapedia.Machines.VersionedValidation
