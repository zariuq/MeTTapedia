import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.NativeWave
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.NativeUpToDead

/-!
# The protocol wave realizes every multi-firing step of the interface up to dead names

`Step/NativeWave` realizes the native concurrent step of a clear family by a protocol wave. The
interface's multi-firing steps up to dead names (`DeadTransport.Concurrent`) ask less than clearness:
each firing is independent, up to dead names, of every later one. That is still enough for the wave.

* **Independence up to dead names makes the commits independent** (`commits_independent_of_independent`):
  if each firing is admitted after the other, neither takes what the other takes or reads, and they make
  different identities.
* **A concurrent word is a sequential run** (`concurrent_sequential`), its firings are admitted at the
  state (`concurrent_admitted`), and its commits are pairwise independent (`concurrent_pairwise`).
* **The protocol wave realizes it** (`interface_protocol_wave`): carried by distinct idle transactions of
  an initial protocol state that holds the state's present occurrences and has not born their fresh
  identities, the word's commits commit in every order, and every order ends with the present
  occurrences of the word's final state.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open NativeIterated NativeDead NativeConcurrent NativeUpToDead

variable {S : Signature} {O : Type} [LinearOrder O] {Γ : Ctx S} {sort : S.Srt}
  [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)] {T : Type*} [DecidableEq T]

namespace NativeWaveInterface

variable {s : NativeState S O Γ sort}

/-- **A firing admitted after another takes nothing the other takes, reads nothing the other takes, and
makes nothing the other makes.** -/
theorem apart_of_after {f g : LiveFiring s} (first : f.toNative.Realized)
    (after : (residualAfter first g).toNative.Realized) :
    (∀ o ∈ f.selection.taken, o ∉ g.selection.taken ∧ o ∉ g.selection.read) ∧
      ∀ o ∈ f.selection.made, o ∉ g.selection.made := by
  obtain ⟨_, enabledF, _, _⟩ := (native_admits_iff f.toNative).mp first
  obtain ⟨_, enabledG, _, _⟩ := (native_admits_iff (residualAfter first g).toNative).mp after
  have present : (native.result f.toNative first).state.present =
      fire s.state.present (f.selection.commit (T := Unit)) := native.present_result f.toNative first
  have gone : ∀ o ∈ f.selection.taken, o ∉ (native.result f.toNative first).state.present := by
    intro o taken inResult
    rw [present] at inResult
    rcases mem_fire.mp inResult with ⟨_, notTaken⟩ | made
    · exact notTaken (List.mem_toFinset.mpr taken)
    · exact Finset.disjoint_left.mp enabledF.fresh made (enabledF.taken_subset (List.mem_toFinset.mpr taken))
  refine ⟨fun o taken => ⟨fun takenG => gone o taken (enabledG.taken_subset (List.mem_toFinset.mpr takenG)),
    fun readG => gone o taken (enabledG.kept_subset (List.mem_toFinset.mpr readG))⟩, fun o made madeG => ?_⟩
  have inResult : o ∈ (native.result f.toNative first).state.present := by
    rw [present]
    exact mem_fire.mpr (Or.inr (List.mem_toFinset.mpr made))
  exact Finset.disjoint_left.mp enabledG.fresh (List.mem_toFinset.mpr madeG) inResult

/-- **Independence up to dead names makes the commits independent.** -/
theorem commits_independent_of_independent {f g : LiveFiring s}
    (independent : DeadTransport.Independent residuals f g) :
    Independent (fun _ : O => ()) (f.selection.commit (T := Unit)) (g.selection.commit (T := Unit)) := by
  obtain ⟨first, second, _, _, rfl, rfl, afterFirst, afterSecond, _⟩ := independent
  obtain ⟨takesF, madeF⟩ := apart_of_after first afterFirst
  obtain ⟨takesG, _⟩ := apart_of_after second afterSecond
  refine ⟨fun clash => clash.elim (fun common => common ?_) (fun common => common ?_), ?_, ?_⟩
  · rw [Finset.disjoint_left]
    intro o takenF takenG
    exact (takesF o (List.mem_toFinset.mp takenF)).1 (List.mem_toFinset.mp takenG)
  · rw [Finset.disjoint_left]
    intro o madeFo madeGo
    exact madeF o (List.mem_toFinset.mp madeFo) (List.mem_toFinset.mp madeGo)
  · rintro (common | ⟨read, member, _⟩)
    · apply common
      rw [Finset.disjoint_left]
      intro o takenF readG
      exact (takesF o (List.mem_toFinset.mp takenF)).2 (List.mem_toFinset.mp readG)
    · simp [Selection.commit] at member
  · rintro (common | ⟨read, member, _⟩)
    · apply common
      rw [Finset.disjoint_left]
      intro o takenG readF
      exact (takesG o (List.mem_toFinset.mp takenG)).2 (List.mem_toFinset.mp readF)
    · simp [Selection.commit] at member

omit [DecidableEq T] in
/-- **A concurrent word is a sequential run.** -/
theorem concurrent_sequential {fs : List (LiveFiring s)} {t : NativeState S O Γ sort}
    (concurrent : DeadTransport.Concurrent residuals s fs t) : Sequential s fs t := by
  induction concurrent with
  | nil s => exact .nil s
  | cons f rest admitted residualList residual _ _ ih =>
      have same := (forall₂_map_iff (residualAfter admitted) rest residualList).mp residual
      subst same
      exact .cons f rest admitted ih

omit [DecidableEq T] in
/-- **The firings of a concurrent word are admitted at the state.** -/
theorem concurrent_admitted {fs : List (LiveFiring s)} {t : NativeState S O Γ sort}
    (concurrent : DeadTransport.Concurrent residuals s fs t) : ∀ f ∈ fs, f.toNative.Realized := by
  cases concurrent with
  | nil => exact fun _ member => absurd member List.not_mem_nil
  | cons f rest admitted _ _ independent _ =>
      intro g member
      rcases List.mem_cons.mp member with rfl | inRest
      · exact admitted
      · obtain ⟨_, second, _⟩ := independent g inRest
        exact second

omit [DecidableEq T] in
/-- **The commits of a concurrent word are pairwise independent.** -/
theorem concurrent_pairwise {fs : List (LiveFiring s)} {t : NativeState S O Γ sort}
    (concurrent : DeadTransport.Concurrent residuals s fs t) :
    fs.Pairwise fun f g => Independent (fun _ : O => ()) (f.selection.commit (T := Unit)) (g.selection.commit (T := Unit)) := by
  induction concurrent with
  | nil s => exact .nil
  | cons f rest admitted residualList residual independent _ ih =>
      have same := (forall₂_map_iff (residualAfter admitted) rest residualList).mp residual
      subst same
      exact List.pairwise_cons.mpr ⟨fun g member => commits_independent_of_independent (independent g member),
        (List.pairwise_map (f := residualAfter admitted)).mp ih⟩

/-- **The protocol wave realizes every multi-firing step of the interface up to dead names**: carried by
distinct idle transactions of an initial protocol state that holds the state's present occurrences and
has not born their fresh identities, the word's commits commit in every order, and every order ends with
the present occurrences of the word's final state. -/
theorem interface_protocol_wave {fs : List (LiveFiring s)} {t : NativeState S O Γ sort}
    (concurrent : DeadTransport.Concurrent residuals s fs t)
    (txn : T → Commit O Unit) {W : List T} (nodup : W.Nodup)
    (carries : W.map txn = fs.map fun f => f.selection.commit (T := Unit))
    (σ : ProtocolState O Unit T) (initial : Initial σ) (store : σ.store = s.state.present)
    (unborn : ∀ t ∈ W, Disjoint (txn t).made σ.born) {order : List T} (perm : order.Perm W) :
    ∃ σ', Run (fun _ : O => ()) txn σ (order.map fun t => (t, txn t)) σ' ∧ σ'.store = t.state.present := by
  have enabledOf : ∀ f ∈ fs, Enabled (fun _ : O => ()) s.state.present (f.selection.commit (T := Unit)) :=
    fun f member => ((native_admits_iff f.toNative).mp (concurrent_admitted concurrent f member)).2.1
  have enabled : ∀ t ∈ W, Enabled (fun _ : O => ()) σ.store (txn t) := by
    intro t member
    have inMap : txn t ∈ fs.map fun f => f.selection.commit (T := Unit) := carries ▸ List.mem_map_of_mem member
    obtain ⟨f, inFs, same⟩ := List.mem_map.mp inMap
    rw [store, ← same]
    exact enabledOf f inFs
  have independent : W.Pairwise fun a b => Independent (fun _ : O => ()) (txn a) (txn b) := by
    apply List.pairwise_map.mp
    rw [carries]
    exact List.pairwise_map.mpr (concurrent_pairwise concurrent)
  obtain ⟨σ', run, final⟩ := protocol_wave nodup σ initial enabled independent unborn perm
  refine ⟨σ', run, final.trans ?_⟩
  rw [carries, store, sequential_present (concurrent_sequential concurrent)]

end NativeWaveInterface

#print axioms NativeWaveInterface.apart_of_after
#print axioms NativeWaveInterface.commits_independent_of_independent
#print axioms NativeWaveInterface.concurrent_sequential
#print axioms NativeWaveInterface.concurrent_admitted
#print axioms NativeWaveInterface.concurrent_pairwise
#print axioms NativeWaveInterface.interface_protocol_wave

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
