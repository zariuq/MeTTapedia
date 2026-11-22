import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Programs.TopLevel
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.RegionPermissions.DelegatedReads
import Mettapedia.GSLT.Timing.IdleWaitCost
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.KeepOnlyCommBoundary

/-!
# Success is an observation, not termination

A program that never stops still succeeds or fails: a test runs beside it and reports on a success
channel. The report is a **barb**: an occurrence in the success region (`Barb`).

* **May-pass** (`MayPass`): some run reaches a store with the barb.
* **Must-pass** (`MustPass`): every fair run reaches it, in the style of De Nicola and Hennessy. A
  run is a run of the commit system with an idle step (`Liveness.LTS.withIdle`), and fair means
  weakly fair for each commit (`Liveness.Run.WeaklyFair`).
* A sequential program's final value is the special case whose test is "the value appears".

## The sequential embedding must-passes the value test

If today's direct evaluation of a program ends with the value in the store, the program's process
(`Chain`) must-passes the value test (`chain_mustPass`): in every fair run each step of the chain
is enabled until it fires, so weak fairness fires it, and the run reaches today's store.

## The test is an await, and it is cheap

An `await` on the success channel is the test. While nothing writes the success channel it costs
no evaluation, however long the program runs (`successAwait_free`, from the wait index of
`GSLT.Timing.IdleWaitCost`, `idle_free`); its memory is one registration (`entries_card`). Checking
every `k` steps is the polling observer, whose cost grows without bound with time
(`IdleWaitCost.Controls.polling_grows`). Both are sound for safety: the await fires only at a
store with the barb (`await_sound`).

The barb must be linear. Once a commit takes the success occurrence the barb is gone
(`Controls.barb_taken`), as rho's communication loses its output barb
(`RhoCalculus.KeepOnlyCommBoundary.comm_loses_output`); a test of facts alone cannot see that loss
(`KeepOnlyCommBoundary.factObservation_not_outputFaithful`). Where nobody takes from the success
region, a barb once present stays (`barb_stays`).

## Detecting a local fixed point while others run

"Await until region `A` has no pending work" is an absence query on `A`. A detector that fires on
it publishes a fixed point; the fixed point stays true under every run of the others exactly when
no one else can ever obtain `send` at `A` (`detection_sound_iff`, by
`RegionPermissions.absence_preserved_iff`), or once `A` has been sealed by revoking the others'
`send` (`detection_stable_after_seal`, by `stable_after_seal`). This is stratification: the
detector belongs to a stratum above every maker into `A`. A late arrival falsifies a detected
fixed point otherwise (`Controls.late_arrival`).

## The answer of an await is determinate where the region is

In a conflict-free system, whether an await fires, and the store it leaves, do not depend on the
schedule (`await_determinate`). The system theorem of `Determinacy` gives conflict-freedom when the
awaited region is a Kahn or monotone name and the processes are determinate on their own.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Programs

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Liveness
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.InteractionTypes

universe uO uR

section Success

variable {O : Type uO} [DecidableEq O] {R : Type uR} (label : O → R)

/-- **A barb**: the store holds an occurrence in the success region. -/
def Barb (success : R → Bool) (store : Finset O) : Prop := ∃ o ∈ store, success (label o) = true

/-- A commit system as a transition system. -/
def commitSystem (sys : Commit O R → Prop) : LTS (Finset O) (Commit O R) where
  Allowed store c := sys c ∧ Enabled label store c
  next store c := fire store c

/-- **May-pass**: some run reaches the barb. -/
def MayPass (sys : Commit O R → Prop) (success : R → Bool) (store : Finset O) : Prop :=
  ∃ t, Reaches label sys store t ∧ Barb label success t

/-- **Must-pass**: every run with an idle step, weakly fair for each commit, reaches the barb. -/
def MustPass (sys : Commit O R → Prop) (success : R → Bool) (store : Finset O) : Prop :=
  ∀ r : Run (commitSystem label sys).withIdle, r.state 0 = store →
    (∀ c, sys c → r.WeaklyFair (LTS.liftTask (· = c))) → ∃ n, Barb label success (r.state n)

variable {label}

/-- A barb in the store stays after a commit that takes nothing from the success region. -/
theorem barb_stays {success : R → Bool} {store : Finset O} {c : Commit O R}
    (noTake : ∀ o ∈ c.taken, success (label o) = false) (barb : Barb label success store) :
    Barb label success (fire store c) := by
  obtain ⟨o, inStore, isSuccess⟩ := barb
  refine ⟨o, mem_fire.mpr (Or.inl ⟨inStore, fun taken => ?_⟩), isSuccess⟩
  rw [noTake o taken] at isSuccess
  exact absurd isSuccess (by decide)

/-- **The await is sound**: a test that keeps or takes a success occurrence fires only at a store
with the barb. -/
theorem await_sound {success : R → Bool} {store : Finset O} {test : Commit O R} {o : O}
    (enabled : Enabled label store test) (uses : o ∈ test.uses) (isSuccess : success (label o) = true) :
    Barb label success store := by
  rcases Commit.mem_uses.mp uses with taken | kept
  · exact ⟨o, enabled.taken_subset taken, isSuccess⟩
  · exact ⟨o, enabled.kept_subset kept, isSuccess⟩

/-! ## The sequential embedding must-passes the value test -/

omit [DecidableEq O] in
/-- A commit's task holds of a label exactly when the label is that commit. -/
theorem liftTask_eq_iff {c : Commit O R} {l : Option (Commit O R)} :
    LTS.liftTask (· = c) l ↔ l = some c := by
  cases l <;> simp [LTS.liftTask]

section Chain

variable {tok : ℕ → O} {effects : List (Commit O R)} {initial : Finset O}

/-- Along a run of the chain with an idle step, a store with token `k` stays until step `k` fires. -/
theorem chain_waits (injective : Function.Injective tok)
    (r : Run (commitSystem label (fun c => c ∈ chain tok 0 effects)).withIdle) {k : ℕ}
    {data : Finset O} (free : TokenFree tok data) {N : ℕ} (at₀ : r.state N = insert (tok k) data)
    (h : k < effects.length) :
    ∀ n, N ≤ n → (∀ m, N ≤ m → m < n →
      r.label m ≠ some (threaded (tok k) (tok (k + 1)) effects[k])) → r.state n = insert (tok k) data := by
  intro n le before
  induction n, le using Nat.le_induction with
  | base => exact at₀
  | succ n le ih =>
      have atN := ih fun m lo hi => before m lo (by omega)
      have allowed := r.allowed n
      rw [r.step n]
      cases hl : r.label n with
      | none => simp only [LTS.withIdle]; exact atN
      | some c =>
          rw [hl] at allowed
          obtain ⟨member, enabled⟩ := allowed
          rw [atN] at enabled
          obtain ⟨_, same⟩ := chain_enabled_unique injective free member enabled
          exact absurd (hl.trans (congrArg some same)) (before n le (by omega))

/-- **The sequential embedding must-passes the value test.** If today's direct evaluation ends with
the value in the store, every fair run of the program's process reaches it. -/
theorem chain_mustPass (injective : Function.Injective tok) (free : TokenFree tok initial)
    (apart : ∀ e ∈ effects, EffectApart label tok e) (today : Executable label initial effects)
    {success : R → Bool} (value : Barb label success (fireList initial effects)) :
    MustPass label (fun c => c ∈ chain tok 0 effects) success (insert (tok 0) initial) := by
  classical
  intro r start fair
  -- after `k` steps of the chain, some moment holds token `k` and the first `k` effects' store
  have reach : ∀ k, k ≤ effects.length →
      ∃ n, r.state n = insert (tok k) (fireList initial (effects.take k)) := by
    intro k
    induction k with
    | zero => intro _; exact ⟨0, by simpa using start⟩
    | succ k ih =>
        intro le
        obtain ⟨N, atN⟩ := ih (by omega)
        have h : k < effects.length := by omega
        have freeK : TokenFree tok (fireList initial (effects.take k)) :=
          fireList_tokenFree free fun e m => apart e (List.mem_of_mem_take m)
        have apartK : EffectApart label tok effects[k] := apart _ (List.getElem_mem h)
        have enabledEffect : Enabled label (fireList initial (effects.take k)) effects[k] := by
          have split := executable_append_iff.mp (by rwa [List.take_append_drop] : Executable label initial
            (effects.take k ++ effects.drop k))
          rw [List.drop_eq_getElem_cons h] at split
          exact (executable_cons_iff.mp split.2).1
        have enabledStep := (threaded_enabled_iff injective freeK apartK k).mpr enabledEffect
        have memberStep : threaded (tok k) (tok (k + 1)) effects[k] ∈ chain tok 0 effects :=
          mem_chain.mpr ⟨k, h, by simp⟩
        have waits := chain_waits injective r freeK atN h
        -- weak fairness fires the step
        obtain ⟨n₁, le₁, fires⟩ := Run.WeaklyFair.fires (fair _ memberStep) N fun n le before => by
          refine ⟨some _, rfl, ?_⟩
          rw [waits n le fun m lo hi same => before m lo hi (liftTask_eq_iff.mpr same)]
          exact ⟨memberStep, enabledStep⟩
        -- the first firing at or after `N`
        have exists_first : ∃ n, N ≤ n ∧ r.label n = some (threaded (tok k) (tok (k + 1)) effects[k]) :=
          ⟨n₁, le₁, liftTask_eq_iff.mp fires⟩
        let first := Nat.find exists_first
        have firstSpec := Nat.find_spec exists_first
        have atFirst : r.state first = insert (tok k) (fireList initial (effects.take k)) :=
          waits first firstSpec.1 fun m lo hi same =>
            Nat.find_min exists_first hi ⟨lo, same⟩
        refine ⟨first + 1, ?_⟩
        rw [r.step first]
        show (commitSystem label _).withIdle.next (r.state first) (r.label first) = _
        rw [firstSpec.2, atFirst]
        show fire _ _ = _
        rw [fire_threaded freeK, List.take_succ_eq_append_getElem h, fireList_append]
        simp
  obtain ⟨n, atEnd⟩ := reach effects.length le_rfl
  rw [List.take_length] at atEnd
  obtain ⟨o, inStore, isSuccess⟩ := value
  exact ⟨n, o, by rw [atEnd]; exact Finset.mem_insert_of_mem inStore, isSuccess⟩

end Chain

end Success

/-! ## Detecting a local fixed point while others run -/

section FixedPoint

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.RegionPermissions
open Mettapedia.Machines.Kernel

variable {O : Type} [DecidableEq O] {R : Type} {N : Type} [DecidableEq N] {Sub : Type}
  [DecidableEq Sub] {label : O → R} {loc : R → N}

/-- The detector: it queries that the names of `A` hold nothing and publishes `done`. -/
def detector (A : N → Bool) (done : O) : Commit O R := ⟨∅, ∅, {done}, [⟨fun r => A (loc r), ∅⟩]⟩

/-- **When a detected fixed point is a fixed point.** After the detector fires, the region stays
empty under every run of the others exactly when no other subject can ever obtain `send` at its
names. -/
theorem detection_sound_iff {st₀ : Delegation.State Sub (Facet × N)} {owner : Sub} {A : N → Bool}
    {store : Finset O} {done : O} (doneOutside : A (loc (label done)) = false)
    (fires : Enabled label store (detector (loc := loc) A done))
    (freshAt : ∀ n, A n = true → ∃ o, o ∉ fire store (detector (loc := loc) A done) ∧ loc (label o) = n) :
    (∀ acts caps' store', SysRun label loc st₀ (fire store (detector (loc := loc) A done)) acts caps' store' →
        OthersActs owner acts → restrict label loc A store' = ∅) ↔
      ∀ b, b ≠ owner → ∀ n, A n = true → ¬ Delegation.CanHold st₀ b (facetAt .send n) false := by
  have empty : restrict label loc A store = ∅ := by
    have holds := fires.queries_hold ⟨fun r => A (loc r), ∅⟩ (by simp [detector])
    exact holds
  have unchanged : restrict label loc A (fire store (detector (loc := loc) A done)) =
      restrict label loc A store := by
    rw [restrict_eq_regionOf, restrict_eq_regionOf]
    refine regionOf_fire_of_no_write fun o written => ?_
    simp only [detector, Finset.empty_union, Finset.mem_singleton] at written
    subst written
    exact doneOutside
  exact absence_preserved_iff (by rw [unchanged, empty]) freshAt

/-- **After sealing, a detected fixed point stays.** -/
theorem detection_stable_after_seal {owner : Sub} {A : N → Bool}
    {caps caps' : Delegation.State Sub (Facet × N)} {store store' : Finset O}
    {acts : List (Act Sub O R N)} (run : SysRun label loc caps store acts caps' store')
    (sealed : Sealed caps owner A) (others : OthersActs owner acts)
    (respects : RespectsSealActs owner A acts) (empty : restrict label loc A store = ∅) :
    restrict label loc A store' = ∅ := by
  have antitone : DownwardClosed (fun B : Finset O => B = ∅) := by
    intro small large sub isEmpty
    subst isEmpty
    exact Finset.subset_empty.mp sub
  exact (stable_after_seal antitone run sealed others respects empty).1

end FixedPoint

/-! ## The answer of an await is determinate where the region is -/

section Determinate

variable {O : Type uO} [DecidableEq O] {R : Type uR} {label : O → R}

/-- **The answer of an await is determinate in a conflict-free system**: whether it fires, and the
store it leaves, do not depend on the schedule. -/
theorem await_determinate {sys : Commit O R → Prop} {store : Finset O}
    (free : ConflictFree label sys store) {first second : List (Commit O R)}
    (maxFirst : Maximal label sys store first) (maxSecond : Maximal label sys store second)
    (await : Commit O R) :
    (await ∈ first ↔ await ∈ second) ∧ fireList store first = fireList store second := by
  obtain ⟨perm, same⟩ := free.maximal_agree maxFirst maxSecond
  exact ⟨perm.mem_iff, same⟩

end Determinate

/-! ## The success await in the wait index -/

section Cost

open Mettapedia.GSLT.Timing.IdleWaitCost

/-- The success key, and the one parked await on it. -/
def successRegs : Unit → Finset Bool := fun _ => {true}

/-- **The success await costs nothing until success is written**: in any run of idle ticks and
commits that do not write the success key, the parked await is evaluated zero times. -/
theorem successAwait_free :
    ∀ events : List (Event Bool Unit), (∀ w, Event.commit w ∈ events → true ∉ w) →
      (∀ f, Event.park f ∉ events) → (∀ f, Event.leave f ∉ events) →
      evaluations successRegs ⟨{()}, {(true, ())}⟩ events = 0
  | [], _, _, _ => rfl
  | e :: rest, noWrite, noPark, noLeave => by
      have restFree := successAwait_free rest (fun w m => noWrite w (List.mem_cons_of_mem _ m))
        (fun f m => noPark f (List.mem_cons_of_mem _ m)) (fun f m => noLeave f (List.mem_cons_of_mem _ m))
      cases e with
      | idle =>
          simpa [evaluations, run, Mettapedia.GSLT.Timing.IdleWaitCost.step, evaluationsOf] using restFree
      | commit w =>
          have notWritten := noWrite w List.mem_cons_self
          simp only [evaluations, run, Mettapedia.GSLT.Timing.IdleWaitCost.step, evaluationsOf]
            at restFree ⊢
          rw [restFree]
          simp [notWritten]
      | park f => exact absurd List.mem_cons_self (noPark f)
      | leave f => exact absurd List.mem_cons_self (noLeave f)

end Cost

/-! ## Controls -/

namespace Controls

open Mettapedia.Languages.ProcessCalculi.RhoCalculus.KeepOnlyCommBoundary

/-- The success region: identity `9`, or anything labelled `true`. -/
def isSuccess : Bool → Bool := id

/-- Labels: `9` is a success occurrence, everything else is not. -/
def flag (o : ℕ) : Bool := o == 9

/-- **The barb is linear, in both models.** Taking the success occurrence removes the barb, as
rho's communication removes its output barb. -/
theorem barb_taken (n q : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern) :
    (Barb flag isSuccess ({9} : Finset ℕ) ∧
        ¬ Barb flag isSuccess (fire ({9} : Finset ℕ) (⟨{9}, ∅, ∅, []⟩ : Commit ℕ Bool))) ∧
      (OutputOn n (redex n q) ∧ ¬ OutputOn n contractum) := by
  refine ⟨⟨⟨9, by decide, rfl⟩, ?_⟩, comm_loses_output n q⟩
  rintro ⟨o, inStore, _⟩
  simp [fire] at inStore

/-- The region of pending work, and an output. -/
inductive Work where
  | pending
  | done
  deriving DecidableEq, Repr

def cellOf : ℕ → Work
  | 7 => .done
  | _ => .pending

def isPending : Work → Bool
  | .pending => true
  | .done => false

/-- The detector: no pending work, then `done` (identity `7`). -/
def detect : Commit ℕ Work := ⟨∅, ∅, {7}, [⟨isPending, ∅⟩]⟩

/-- A late maker adds pending work (identity `5`). -/
def lateMake : Commit ℕ Work := Commit.makeOne 5

/-- **Negative control, a late arrival.** The detector fires on an empty region and publishes
`done`; a maker that could still send adds work afterwards, and the published fixed point is
false. -/
theorem late_arrival :
    Executable cellOf ∅ [detect, lateMake] ∧ 7 ∈ fireList (∅ : Finset ℕ) [detect, lateMake] ∧
      regionOf cellOf (fireList (∅ : Finset ℕ) [detect, lateMake]) isPending ≠ ∅ := by
  refine ⟨.cons (by decide) (.cons (by decide) (.nil _)), by decide, by decide⟩

/-- **Positive control.** Without the late maker the region stays empty after detection. -/
theorem no_late_maker :
    Executable cellOf ∅ [detect] ∧
      regionOf cellOf (fireList (∅ : Finset ℕ) [detect]) isPending = ∅ := by
  exact ⟨.cons (by decide) (.nil _), by decide⟩

end Controls

end Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Programs
