import Mettapedia.Machines.VersionedValidation.Versions

/-!
# Stamps under concurrency

## Taking a stamp of several counters

Counters never decrease. A reader that reads each counter once, at staggered
cuts, can observe a vector that existed at no single cut
(`Controls.single_collect_inconsistent`). A double collect reads each counter at
both ends of a window. Monotone counters are a discipline for themselves
(`counter_discipline`), so the double collect is `agrees_at_jointStart` of
`ReadWindowCuts` for that discipline: cross-ordered windows with equal end reads
observe every counter at the joint start (`Controls.double_collect_instance`), and
a joint start exists exactly when the windows are cross-ordered
(`Window.exists_joint_iff`). A consistent collect is the stamp `takeStamp` takes
at its cut (`collectedStamp_eq_takeStamp`). One global counter needs a single read
(`single_counter_single_read`).

## Ordering a write against a read

For one key, a writer publishes at cut `w` and bumps the version at cut `b`; a
reader stamps at `s`, reads at `r` and validates at `u ≥ r`. This single write is
the single-region instance of the ordering law `sound_of_delayed_bumps`: with
publish-then-bump (`w ≤ b`) and stamp-then-read (`s ≤ r`), equal versions at `s`
and `u` give equal values at `r` and `u` whenever `u` is not inside the in-flight
window `[w, b)` (`publish_then_bump_sound`). Inside it the read may disagree with
the store (`Controls.inflight_validation_differs`). The synchronous case `w = b`
leaves no window; it is exactly the case in which the write is a discipline
(`singleWrite_discipline_iff`), so `sound_of_sample_then_confirm` applies
(`Controls.atomic_write_instance`). A delayed bump is outside the discipline and
inside the ordering law (`Controls.publish_then_bump_beyond_discipline`).

Both orderings are necessary uniformly. Stamp first is
`uniform_soundness_iff_sample_first`. Publish first is
`uniform_soundness_iff_publish_first`: bumping before publishing accepts a stale
value after the write completed (`Controls.bump_before_publish_is_stale`).
-/

set_option autoImplicit false

namespace Mettapedia.Machines.VersionedValidation

open ReadOnlyQuery
open Mettapedia.GSLT.Contracts.ReadWindowCuts (Cut Discipline Window recordedReads
  agrees_at_jointStart)

universe u v w

/-! ## Collecting counters -/

section DoubleCollect

variable {steps : ℕ} {K : Type w}

/-- The vector observed by reading counter `k` at cut `time k`. -/
def collect (counter : Cut steps → K → ℕ) (time : K → Cut steps) : K → ℕ :=
  fun k => counter (time k) k

/-- On the listed counters, the observed vector is the state at the single cut `T`. -/
def ConsistentAt (counter : Cut steps → K → ℕ) (keys : List K) (observed : K → ℕ)
    (T : Cut steps) : Prop :=
  ∀ k ∈ keys, observed k = counter T k

/-- Counters that never decrease are a discipline for themselves. -/
theorem counter_discipline {counter : Cut steps → K → ℕ}
    (mono : ∀ (i : Fin steps) k, counter i.castSucc k ≤ counter i.succ k) :
    Discipline counter (fun k => ({k} : Set K)) counter :=
  ⟨mono, fun _ k same => same (Set.mem_singleton k)⟩

/-- **One global counter needs a single read.** With only one counter, any single
collect is the state at the cut of its read. -/
theorem single_counter_single_read [Subsingleton K] (counter : Cut steps → K → ℕ)
    (time : K → Cut steps) (keys : List K) :
    ∃ T, ConsistentAt counter keys (collect counter time) T := by
  cases keys with
  | nil => exact ⟨0, fun _ member => by cases member⟩
  | cons k _ =>
      refine ⟨time k, fun k' _ => ?_⟩
      rw [Subsingleton.elim k' k]
      rfl

/-- A consistent collect of the counters of the classes read is the stamp taken at
the cut, for the versioning `counter`. -/
theorem collectedStamp_eq_takeStamp {Key : Type u} {Value : Type v} [DecidableEq K]
    {counter : Cut steps → K → ℕ} {cls : Key → K} {reads : Reads Key Value}
    {observed : K → ℕ}
    {T : Cut steps} (consistent : ConsistentAt counter (classes cls reads) observed T) :
    (classes cls reads).map (fun k => (k, observed k)) = takeStamp cls counter T reads := by
  unfold takeStamp
  apply List.map_congr_left
  intro k member
  rw [consistent k member]

end DoubleCollect

/-! ## A single write -/

section Ordering

variable {steps : ℕ} {α : Type u}

/-- The value of one key: `old` before the publication at cut `w`, `new` from `w`. -/
def valueAt (old new : α) (w : ℕ) (t : Cut steps) : α :=
  if (t : ℕ) < w then old else new

/-- The version of one key: `v` before the bump at cut `b`, `v + 1` from `b`. -/
def versionAt (v b : ℕ) (t : Cut steps) : ℕ :=
  if (t : ℕ) < b then v else v + 1

theorem versionAt_advance (v b : ℕ) (i : Fin steps) :
    versionAt v b i.castSucc ≤ versionAt v b i.succ := by
  simp only [versionAt, Fin.val_castSucc, Fin.val_succ]
  split_ifs <;> omega

/-- **Publish, then bump; stamp, then read.** The single-region instance of
`sound_of_delayed_bumps`: if `w ≤ b` and `s ≤ r ≤ u`, and the validation at `u` is
not inside the in-flight window `[w, b)`, equal versions at `s` and `u` give equal
values at `r` and `u`. -/
theorem publish_then_bump_sound (old new : α) {v w b : ℕ} {s r u : Cut steps} (order : w ≤ b)
    (stampFirst : s ≤ r) (later : r ≤ u) (quiescent : (u : ℕ) < w ∨ b ≤ u)
    (same : versionAt v b s = versionAt v b u) :
    valueAt old new w r = valueAt old new w u := by
  refine (sound_of_delayed_bumps (view := fun cut (_ : Unit) => valueAt old new w cut)
    (footprint := fun _ => ({()} : Set Unit)) (stamp := fun cut (_ : Unit) => versionAt v b cut)
    (fun i _ => versionAt_advance v b i) () stampFirst later ?_ fun region _ => by
      cases region
      exact same).symm
  intro i lo hi changed
  have upper : (i : ℕ) + 1 ≤ u := by simpa only [Fin.le_def, Fin.val_succ] using hi
  have published : (i : ℕ) + 1 = w := by
    simp only [valueAt, Fin.val_castSucc, Fin.val_succ] at changed
    split_ifs at changed <;> first | omega | exact absurd rfl changed
  have bumpInWord : b - 1 < steps := by
    have := u.isLt
    omega
  refine ⟨⟨b - 1, bumpInWord⟩, ?_, ?_, (), rfl, ?_⟩
  · rw [Fin.le_def]
    simp only
    omega
  · rw [Fin.le_def, Fin.val_succ]
    simp only
    omega
  · simp only [versionAt, Fin.val_castSucc, Fin.val_succ]
    split_ifs <;> omega

/-- A single write is a discipline exactly when it publishes and bumps at the same
cut: the synchronous instance `w = b`. -/
theorem singleWrite_discipline_iff {old new : α} (distinct : old ≠ new) {v w b : ℕ}
    (published : 1 ≤ w) (inWord : w ≤ steps) (bumpedInWord : 1 ≤ b) :
    Discipline (fun cut : Cut steps => fun (_ : Unit) => valueAt old new w cut)
        (fun _ => (Set.univ : Set Unit))
        (fun cut : Cut steps => fun (_ : Unit) => versionAt v b cut) ↔
      w = b := by
  constructor
  · intro discipline
    by_contra different
    have frame := discipline.frame ⟨w - 1, by omega⟩ () (by
      intro _ _
      simp only [Fin.val_castSucc, Fin.val_succ, versionAt]
      split_ifs <;> omega)
    simp only [Fin.val_castSucc, Fin.val_succ, valueAt] at frame
    rw [if_pos (by omega), if_neg (by omega)] at frame
    exact distinct frame
  · rintro rfl
    constructor
    · intro i _
      exact versionAt_advance v w i
    · intro i _ unchanged
      have equal := unchanged (Set.mem_univ ())
      simp only [Fin.val_castSucc, Fin.val_succ, versionAt, valueAt] at equal ⊢
      split_ifs at equal ⊢ <;> first | rfl | omega

/-- **Publish first is necessary and sufficient.** Over all stamp, read and
validation cuts with `s ≤ r ≤ u` and quiescent validation, a single write that
publishes within the word is reused soundly exactly when it publishes no later
than it bumps. A discipline cannot state this: it forces the bump to the step of
the change. -/
theorem uniform_soundness_iff_publish_first {w b : ℕ} (inWord : w ≤ steps) :
    (∀ (v : ℕ) (s r u : Cut steps), s ≤ r → r ≤ u → ((u : ℕ) < w ∨ b ≤ u) →
      versionAt v b s = versionAt v b u → valueAt (0 : ℕ) 1 w r = valueAt 0 1 w u) ↔
      w ≤ b := by
  constructor
  · intro uniformly
    by_contra bumpFirst
    have stale := uniformly 0 ⟨b, by omega⟩ ⟨b, by omega⟩ ⟨w, by omega⟩ le_rfl
      (Fin.mk_le_mk.mpr (by omega)) (Or.inr (by simp only; omega)) (by
        simp only [versionAt]
        rw [if_neg (by omega), if_neg (by omega)])
    simp only [valueAt] at stale
    rw [if_pos (by omega), if_neg (by omega)] at stale
    exact absurd stale (by decide)
  · intro order v s r u stampFirst later quiescent same
    exact publish_then_bump_sound 0 1 order stampFirst later quiescent same

end Ordering

namespace Controls

/-- Counter `false` is bumped at cut 1 and counter `true` at cut 2. -/
def staggered : Cut 4 → Bool → ℕ := fun t k =>
  if k then (if 2 ≤ (t : ℕ) then 1 else 0) else (if 1 ≤ (t : ℕ) then 1 else 0)

theorem staggered_monotone (i : Fin 4) (k : Bool) :
    staggered i.castSucc k ≤ staggered i.succ k := by
  cases k <;> simp only [staggered, Fin.val_castSucc, Fin.val_succ] <;> split_ifs <;> omega

/-- Read counter `false` at cut 0 and counter `true` at cut 2. -/
def staggeredReads : Bool → Cut 4
  | false => 0
  | true => 2

/-- **A single collect is not a cut.** It observes `(0, 1)`, a vector that existed
at no single cut; reading both counters again at cut 3 refuses it. -/
theorem single_collect_inconsistent :
    collect staggered staggeredReads false = 0 ∧ collect staggered staggeredReads true = 1 ∧
      (∀ T, ¬ ConsistentAt staggered [false, true] (collect staggered staggeredReads) T) ∧
      staggered (staggeredReads false) false ≠ staggered 3 false := by
  refine ⟨rfl, rfl, fun T consistent => ?_, by decide⟩
  have atFalse := consistent false (by simp)
  have atTrue := consistent true (by simp)
  simp [collect, staggered, staggeredReads] at atFalse atTrue
  omega

/-- A cross-ordered double collect: counter `false` in the window `[1, 3]`, counter
`true` in `[2, 4]`. -/
def doubleCollectReads : List (Bool × Window (Cut 4)) :=
  [(false, ⟨1, 1, 3, by decide, by decide⟩), (true, ⟨2, 2, 4, by decide, by decide⟩)]

/-- The double collect, `agrees_at_jointStart` for `counter_discipline`, with its
hypotheses met: both pairs of reads are equal, the joint start is cut 2, and both
samples are the counters at cut 2. -/
theorem double_collect_instance :
    Window.jointStart (doubleCollectReads.map Prod.snd) = 2 ∧
      Agrees (staggered (Window.jointStart (doubleCollectReads.map Prod.snd)))
        (recordedReads staggered doubleCollectReads) := by
  refine ⟨by decide, agrees_at_jointStart (counter_discipline staggered_monotone)
    doubleCollectReads ?_ ?_⟩
  · intro entry member
    simp only [doubleCollectReads, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;>
      · intro region inside
        rw [Set.mem_singleton_iff] at inside
        subst inside
        decide
  · intro first firstMember second secondMember
    simp only [doubleCollectReads, List.map_cons, List.map_nil, List.mem_cons,
      List.not_mem_nil, or_false] at firstMember secondMember
    rcases firstMember with rfl | rfl <;> rcases secondMember with rfl | rfl <;> decide

/-- `single_counter_single_read` has content: a single global counter read at cut 1
is the state at cut 1. -/
theorem single_counter_instance :
    ConsistentAt (fun (t : Cut 1) (_ : Unit) => (t : ℕ)) [()]
      (collect (fun (t : Cut 1) (_ : Unit) => (t : ℕ)) fun _ => 1) 1 :=
  fun _ _ => rfl

/-- `publish_then_bump_sound` applies with its hypotheses met: the reader stamps
and reads after the write completed. -/
theorem ordering_instance :
    valueAt (steps := 5) 0 1 1 3 = valueAt (steps := 5) 0 1 1 5 ∧
      versionAt (steps := 5) 4 2 3 = versionAt (steps := 5) 4 2 5 :=
  ⟨publish_then_bump_sound (v := 4) 0 1 (by decide : 1 ≤ 2) (by decide : (3 : Cut 5) ≤ 3)
    (by decide : (3 : Cut 5) ≤ 5) (Or.inr (by decide)) rfl, rfl⟩

/-- The synchronous instance: an atomic write at cut 2 is a discipline, and
`sound_of_sample_then_confirm` certifies the value with no quiescence condition. -/
theorem atomic_write_instance :
    valueAt (steps := 3) (0 : ℕ) 1 2 3 = valueAt (steps := 3) 0 1 2 2 :=
  sound_of_sample_then_confirm
    ((singleWrite_discipline_iff (v := 4) (by decide : (0 : ℕ) ≠ 1) (by decide) (by decide)
      (by decide)).mpr rfl) () (by decide : (2 : Cut 3) ≤ 2) (by decide : (2 : Cut 3) ≤ 3)
    fun _ _ => rfl

/-- Inside the in-flight window `[w, b)` the versions agree and the values differ:
the quiescence hypothesis of `publish_then_bump_sound` cannot be dropped. -/
theorem inflight_validation_differs :
    versionAt (steps := 3) 4 3 0 = versionAt (steps := 3) 4 3 2 ∧
      valueAt (steps := 3) 0 1 1 0 ≠ valueAt (steps := 3) 0 1 1 2 ∧
      versionAt (steps := 3) 4 3 0 ≠ versionAt (steps := 3) 4 3 3 := by
  decide

/-- **Bump before publish is stale.** The reader stamps the bumped version at 1 and
reads the old value at 1; the write publishes at 2. At every validation from cut 3,
after the write completed, the versions agree and the value has changed. -/
theorem bump_before_publish_is_stale :
    ∀ later : Cut 5, 3 ≤ later →
      versionAt 4 1 (1 : Cut 5) = versionAt 4 1 later ∧
        valueAt (0 : ℕ) 1 2 (1 : Cut 5) ≠ valueAt 0 1 2 later := by
  decide

/-- Publish at 1, bump at 2: outside the discipline theory, inside the ordering law. -/
theorem publish_then_bump_beyond_discipline :
    ¬ Discipline (fun cut : Cut 3 => fun (_ : Unit) => valueAt (0 : ℕ) 1 1 cut)
        (fun _ => (Set.univ : Set Unit))
        (fun cut : Cut 3 => fun (_ : Unit) => versionAt 0 2 cut) ∧
      ∀ s r u : Cut 3, s ≤ r → r ≤ u → ((u : ℕ) < 1 ∨ 2 ≤ (u : ℕ)) →
        versionAt 0 2 s = versionAt 0 2 u → valueAt (0 : ℕ) 1 1 r = valueAt 0 1 1 u :=
  ⟨fun discipline => absurd
      ((singleWrite_discipline_iff (by decide : (0 : ℕ) ≠ 1) (by decide) (by decide)
        (by decide)).mp discipline) (by decide),
    fun _ _ _ stampFirst later quiescent same =>
      publish_then_bump_sound 0 1 (by decide) stampFirst later quiescent same⟩

end Controls

end Mettapedia.Machines.VersionedValidation
